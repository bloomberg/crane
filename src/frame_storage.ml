(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a machine's frames hold the parameters of its loops.  See
    [frame_storage.mli]. *)

open Names
open Miniml
module Term = Control_ir.Term
module Loop = Control_ir.Loop

type t = {
  own : Ownership_ir.Storage.t list;
  entered : (int * Ownership_ir.Storage.t) list;
}

type parameter =
  | Own of int
  | Entered of {
      loop : Term.loop;
      index : int;
      level : int;
    }

let rec value_inductive ~abbreviations : ml_type -> bool = function
  | Tglob ((GlobRef.IndRef _ as r), _, _) ->
    (not (Table.is_coinductive r)) && (not (Table.is_custom r)) && not (Table.is_enum_inductive r)
  | Tglob ((GlobRef.ConstRef kn as r), args, _) when abbreviations && not (Table.is_custom r) -> (
    match Table.lookup_typedef_unchecked kn with
    | Some t -> value_inductive ~abbreviations (Mlutil.type_subst_list args t)
    | None -> false )
  | Tmeta {contents = Some t} -> value_inductive ~abbreviations t
  | _ -> false

let passed_holdable passing ty =
  match passing with
  | Some Callable_abi.Borrowed -> value_inductive ~abbreviations:true ty
  | Some Owned -> Table.reuse () && Table.non_atomic_rc () && value_inductive ~abbreviations:true ty
  | Some Forwarded | None -> false

let local_holdable (l : Term.loop) i =
  match l.loop with
  | Loop.Function _ -> None
  | Loop.Member (o, j) ->
    Option.map
      (fun passing ->
        passed_holdable (Option.flatten (List.nth_opt passing i)) (snd (List.nth l.parameters i)) )
      (Ownership_ir.Local_passing.lookup (o, j))

let check_local i ~planned ~declared =
  if Probe.checking () && planned && not (declared ()) then
    Probe.violation "frame storage"
      Pp.(
        str "the plan of a local fixpoint lends its parameter " ++ int i
        ++ str " for a frame to hold by pointer, at a declared type no pointer spells" )

(* What a value the machine holds is, of the storage the caller passed it --
   which outlives the machine, and which nothing changes while it runs: a
   reference into it, a heap cell it owns, a copy of something in it, which
   holds its cells, or none of it. *)
type kind =
  | Stable
  | Cell
  | Shares
  | Fresh

(* A value of kind [k] copied into a local of its own. *)
let copied = function Stable | Cell | Shares -> Shares | Fresh -> Fresh

(* A local of kind [k] kept across a call in a frame, as it was declared: a
   cell is held by the handle the pattern bound, which the frame copies. *)
let kept = function Cell -> Cell | Stable | Shares -> Shares | Fresh -> Fresh

(* The kind of the value a term is, where [env] gives the kind of each Core
   binder in scope: a variable's, through any in-place coercion; anything
   else is computed afresh. *)
let rec kind ~in_place env = function
  | MLrel (db, _) -> Option.default Fresh (List.nth_opt env (db - 1))
  | MLmagic (Mcoerce (from, into), e, _) when in_place from into -> kind ~in_place env e
  | _ -> Fresh

(* Whether a frame may hold a pointer to a value of this kind. *)
let pointable = function Stable | Cell -> true | Shares | Fresh -> false

(* The constructor each binder of [b] is bound at, with its declared
   argument, [Prel 1] first, where the pattern binds it directly. *)
let declared_arguments (b : Term.branch) =
  let count = List.length b.binders in
  let bound = Array.make count None in
  let at r j k = if k >= 1 && k <= count then bound.(k - 1) <- Some (r, j) in
  ( match b.pattern with
  | Pcons (r, ps) -> List.iteri (fun j -> function Prel k -> at r j k | _ -> ()) ps
  | Pusual r -> List.iteri (at r) (List.init count (fun i -> count - i))
  | Pwild | Prel _ | Ptuple _ -> () );
  Array.to_list bound

(* The binders of the branch [b] of a match on a value of kind [k] and type
   [ty], [Prel 1] first.  A variant's fields are bound by reference into the
   value: one stored behind the pointer is a cell wherever the value holds
   the storage's cells, any other lies where the value does.  A record's
   fields may be bound as copies, and a custom match binds what its
   template computes. *)
let branch_binders ~pointer_fields ty k (b : Term.branch) =
  let record = Table.record_fields_of_type ty <> [] in
  let custom = function GlobRef.ConstructRef (ind, _) -> Table.is_custom (GlobRef.IndRef ind) | _ -> false in
  List.map
    (function
      | Some (r, j) when not (custom r) ->
        if List.mem j (Option.default [] (pointer_fields r)) then (match k with Fresh -> Fresh | _ -> Cell)
        else if record then copied k
        else (match k with Cell -> Stable | k -> k)
      | Some _ | None -> Fresh )
    (declared_arguments b)

(* A loop's parameter: the loop, and its position. *)
let same_parameter (l, i) (l', i') = Loop.equal l l' && Int.equal i i'

let mem p ps = List.exists (same_parameter p) ps

(* The binders the body of a loop an entry enters stands under besides the
   loop's parameters: a local fixpoint's name. *)
let named (l : Term.loop) = match l.loop with Loop.Member _ -> 1 | Loop.Function _ -> 0

(* The parameters of the loops [l] and its entries pass a value [pointed]
   does not hold pointable to, each with the Core level it is bound at:
   [pointed] says which are held by pointer, the others by value, fresh. *)
let unpointable ~pointer_fields ~in_place ~pointed (l : Term.loop) =
  let bad = ref [] in
  let params (lp : Term.loop) = List.mapi (fun i _ -> if pointed (lp.loop, i) then Stable else Fresh) lp.parameters in
  let rec walk env = function
    | Term.Loop inner -> walk (List.rev (params inner) @ env) inner.body
    | Let b -> walk (copied (kind ~in_place env b.value) :: env) b.body
    | Match m ->
      let k = kind ~in_place env m.scrutinee in
      List.iter (fun (b : Term.branch) -> walk (branch_binders ~pointer_fields m.scrutinee_type k b @ env) b.body) m.branches
    | Return _ -> ()
    | Continue c | Continue_into {next = c; _} ->
      List.iteri
        (fun i a -> if not (pointable (kind ~in_place env a)) && not (mem (c.target, i) !bad) then bad := (c.target, i) :: !bad)
        c.arguments
    | Resume r ->
      walk env r.value;
      walk (Fresh :: List.map kept env) r.body
    | Entry e ->
      walk (Option.cata (fun _ -> [Fresh]) [] e.name @ env) e.scope;
      (* The entered body runs from frames: what it reads of the scope was
         kept in them. *)
      walk (List.rev (params e.entered) @ List.init (named e.entered) (fun _ -> Fresh) @ List.map kept env) e.entered.body
  in
  walk (List.rev (params l)) l.body;
  !bad

(* The Core levels of the parameters of each loop [l]'s entries enter,
   standing under the loop's parameters. *)
let entered_levels (l : Term.loop) =
  let rec go depth acc = function
    | Term.Loop inner -> go (depth + List.length inner.parameters) acc inner.body
    | Let b -> go (depth + 1) acc b.body
    | Match m -> List.fold_left (fun acc (b : Term.branch) -> go (depth + List.length b.binders) acc b.body) acc m.branches
    | Return _ | Continue _ | Continue_into _ -> acc
    | Resume r -> go (depth + 1) (go depth acc r.value) r.body
    | Entry e ->
      let base = depth + named e.entered in
      let acc = List.mapi (fun i _ -> ((e.entered, i), base + i)) e.entered.parameters @ acc in
      let acc = go (base + List.length e.entered.parameters) acc e.entered.body in
      go (depth + Option.cata (fun _ -> 1) 0 e.name) acc e.scope
  in
  go (List.length l.parameters) [] l.body

let plan ~pointer_fields ~in_place ~holdable (l : Term.loop) =
  let levels = entered_levels l in
  (* What a frame cannot hold by pointer is held by value from the start. *)
  let unholdable =
    List.filter_map (fun i -> if holdable (Own i) then None else Some (l.loop, i)) (List.init (List.length l.parameters) Fun.id)
    @ List.filter_map
        (fun (((loop : Term.loop), index), level) ->
          if holdable (Entered {loop; index; level}) then None else Some (loop.loop, index) )
        levels
  in
  (* The greatest set of parameters held by pointer: each passed only what
     is pointable when those are. *)
  let rec settle excluded =
    let pointed p = not (mem p excluded) in
    match List.filter (fun p -> not (mem p excluded)) (unpointable ~pointer_fields ~in_place ~pointed l) with
    | [] -> excluded
    | more -> settle (more @ excluded)
  in
  let excluded = settle unholdable in
  let storage p : Ownership_ir.Storage.t = if mem p excluded then Frame else Local in
  { own = List.mapi (fun i _ -> storage (l.loop, i)) l.parameters;
    entered = List.map (fun (((loop : Term.loop), i), level) -> (level, storage (loop.loop, i))) levels }
