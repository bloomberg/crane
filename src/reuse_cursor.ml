(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Perceus reuse cursor of a loop built tail modulo cons.  See
    [reuse_cursor.mli]. *)

open Miniml
module Term = Control_ir.Term

type action =
  | Recycle of {cells_read_first : (int * int) list}
  | Release

type step = {
  turn : Occurrence.t;
  action : action;
  arguments_read_first : int list;
}

type t = {
  parameter : int;
  steps : step list;
}

(* Where, of the cell the cursor stands on, a value lies: the whole cell,
   the field a match on the cursor binds to the binder at [level], stored
   behind the pointer or not, or in what the field at [level] points at. *)
type part =
  | Whole
  | Field of {level : int; pointer : bool}
  | Pointee of int

(* A binder inside the loop's parameters, of a loop walking the parameter
   [cursor]: whether it is the cursor itself, the level of a field stored
   behind the pointer it is, where a match on the cursor binds one, and
   what of the cell its value lies in or refers into. *)
type binder = {
  cursor : bool;
  pointer_field : int option;
  parts : part list;
}

let unrelated = {cursor = false; pointer_field = None; parts = []}

(* The parts of the cell [e], standing under [env], reads, through every
   variable it reads, a closure's captures included. *)
let reads env e =
  let rec go depth acc = function
    | MLrel (db, _) ->
      if db > depth then match List.nth_opt env (db - depth - 1) with Some b -> b.parts @ acc | None -> acc
      else acc
    | MLlam (_, _, b) -> go (depth + 1) acc b
    | MLletin (_, _, a, b, _) -> go (depth + 1) (go depth acc a) b
    | MLcase (_, s, branches, _) ->
      Array.fold_left (fun acc (ids, _, _, b) -> go (depth + List.length ids) acc b) (go depth acc s) branches
    | MLfix (_, ids, funs, _, _) -> Array.fold_left (go (depth + Array.length ids)) acc funs
    | MLapp (f, args) -> List.fold_left (go depth) acc (f :: args)
    | MLcons (_, _, args) | MLtuple args -> List.fold_left (go depth) acc args
    | MLmagic (_, e) -> go depth acc e
    | MLparray (elements, default) -> Array.fold_left (go depth) (go depth acc default) elements
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLnumeral _ | MLfloat _ | MLstring _ -> acc
  in
  go 0 [] e

(* [e] without the in-place coercions around it: they change nothing a
   parameter stands for. *)
let rec strip ~in_place = function
  | MLmagic (Mcoerce (from, into), e) when in_place from into -> strip ~in_place e
  | e -> e

(* The declared argument of its constructor each binder of [b] is bound at,
   [Prel 1] first, where the pattern binds it directly at one. *)
let declared_arguments (b : Term.branch) =
  let count = List.length b.binders in
  let bound = Array.make count None in
  let at r j k = if k >= 1 && k <= count then bound.(k - 1) <- Some (r, j) in
  ( match b.pattern with
  | Pcons (r, ps) -> List.iteri (fun j -> function Prel k -> at r j k | _ -> ()) ps
  | Pusual r -> List.iteri (at r) (List.init count (fun i -> count - i))
  | Pwild | Prel _ | Ptuple _ -> () );
  Array.to_list bound

(* The binders of the branch [b] of a match on [scrutinee], [Prel 1]
   first, under [env].  A match on the cursor itself binds its fields; one
   on anything else binds parts of what it reads, a field stored behind the
   pointer leading to what it points at.  A binder a match on the cursor
   binds otherwise than at a field of its constructor may be any of it. *)
let branch_binders ~pointer_fields ~in_place env scrutinee (b : Term.branch) =
  let base = List.length env and count = List.length b.binders in
  let on_cursor =
    match strip ~in_place scrutinee with
    | MLrel (db, _) -> ( match List.nth_opt env (db - 1) with Some {cursor; _} -> cursor | None -> false )
    | _ -> false
  in
  if on_cursor then
    List.mapi
      (fun i declared ->
        let level = base + count - (i + 1) in
        match declared with
        | Some (r, j) ->
          let pointer = List.mem j (Option.default [] (pointer_fields r)) in
          { cursor = false;
            pointer_field = (if pointer then Some level else None);
            parts = [Field {level; pointer}] }
        | None -> {unrelated with parts = [Whole]} )
      (declared_arguments b)
  else
    let parts =
      List.map (function Field {level; pointer = true} -> Pointee level | p -> p) (reads env scrutinee)
    in
    List.map (fun _ -> {unrelated with parts}) b.binders

(* Whether reading [parts] reads the field at [field] itself, or the whole
   cell: what the steal leaves empty. *)
let reads_stolen ~field = List.exists (function Whole -> true | Field {level; _} -> level = field | Pointee _ -> false)

(* Whether reading [parts] reads anything the cell holds once the field at
   [field] has been stolen out of it: what the cell's rebuilding destroys.
   What the stolen field points at outlives it. *)
let reads_cell ~field = List.exists (function Whole | Field _ -> true | Pointee level -> level <> field)

(* Whether a let binding [value] at [ty] holds a value of its own, which
   reading later reads nothing of the cell: the let is evaluated where it
   stands, before the turn steals the field and rebuilds or releases the
   cell, into a C++ local declared by value.  Not so where the let may be a
   reference into what it reads, or a closure that reads it later:
   - a field projected out of a variable, which the plan binds by const
     reference ({!Ownership_ir.projects_in_place}) -- any projection, as
     whether it does is the plan's;
   - a variable read as it is, or a match, which may yield one of its
     fields;
   - a custom head whose text declares the binder itself (a block
     template) or yields its argument or a field of it;
   - a function value, or anything holding a lambda or a fixpoint: a closure
     may capture what it reads by reference (a single-use partial
     application does, translation's [&] capture).
   A call's result, a construction or a literal over none of those is a
   value of its own; one that is a handle to a cell holds its own count. *)
let own_value ty value =
  let rec closure_free = function
    | MLlam _ | MLfix _ -> false
    | MLapp (f, args) -> List.for_all closure_free (f :: args)
    | MLcons (_, _, args) | MLtuple args -> List.for_all closure_free args
    | MLmagic (_, e) -> closure_free e
    | MLletin (_, _, a, b, _) -> closure_free a && closure_free b
    | MLcase (_, s, branches, _) -> closure_free s && Array.for_all (fun (_, _, _, b) -> closure_free b) branches
    | MLparray (elements, default) -> Array.for_all closure_free elements && closure_free default
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLnumeral _ | MLfloat _ | MLstring _ -> true
  in
  let rec head = function MLmagic (_, e) -> head e | e -> e in
  (* A custom computes a value of its own unless its text binds the result
     itself or yields its argument, or a field of it, as an lvalue. *)
  let computes r =
    match Table.find_custom_opt r with
    | None -> true
    | Some text -> (
      let t = Minicpp.inline_template text in
      match (t.it_form, t.it_shape) with
      | Block_iife, _ | _, (Inline_identity | Inline_pair_projection _) -> false
      | (Templated | Bare_callee), Inline_other -> true )
  in
  let fresh =
    match head value with
    | MLapp (MLglob {callee; _}, _) -> computes callee
    | MLapp (MLrel _, _) -> true
    | MLcons (_, r, _) -> computes r
    | MLtuple _ | MLuint _ | MLnumeral _ | MLfloat _ | MLstring _ -> true
    | _ -> false
  in
  fresh && (not (Ml_type_util.is_prod_ml_type ty)) && closure_free value

exception Not_walked

(* The steps of the loop [l] walking its parameter [cursor], every turn of
   [l] passing it itself or a field stored behind the pointer of a match on
   it; [Not_walked] where one passes it anything else, or walks it on
   building a cell of another type than the cursor's. *)
let steps ~pointer_fields ~in_place (l : Term.loop) cursor =
  let n = List.length l.parameters in
  let cursor_type = snd (List.nth l.parameters cursor) in
  let passed env (c : Term.continue_) =
    if not (Control_ir.Loop.equal c.target l.loop) then raise Not_walked;
    match Option.map (strip ~in_place) (List.nth_opt c.arguments cursor) with
    | Some (MLrel (db, _)) -> (
      match List.nth_opt env (db - 1) with
      | Some {cursor = true; _} -> None
      | Some {pointer_field = Some field; _} -> Some field
      | Some _ | None -> raise Not_walked )
    | Some _ | None -> raise Not_walked
  in
  let step env (next : Term.continue_) field action =
    let arguments_read_first =
      List.filter_map
        (fun (i, a) -> if i <> cursor && reads_cell ~field (reads env a) then Some i else None)
        (List.mapi (fun i a -> (i, a)) next.arguments)
    in
    {turn = next.occurrence; action; arguments_read_first}
  in
  let recycle env result (into : Term.continue_into) field =
    ( match result with
    | Some ty when into.cells <> [] && Mlutil.eq_ml_type ty cursor_type -> ()
    | Some _ | None -> raise Not_walked );
    let cells_read_first =
      List.concat
        (List.mapi
           (fun k (cell : Term.cell) ->
             let read_first = if k = 0 then reads_stolen ~field else reads_cell ~field in
             List.filter_map
               (fun (m, a) ->
                 let j = if m < cell.hole then m else m + 1 in
                 if read_first (reads env a) then Some (k, j) else None )
               (List.mapi (fun m a -> (m, a)) cell.arguments) )
           into.cells )
    in
    step env into.next field (Recycle {cells_read_first})
  in
  let rec walk env result acc = function
    | Term.Let b ->
      let parts = if own_value b.binder_type b.value then [] else reads env b.value in
      walk ({unrelated with parts} :: env) result acc b.body
    | Match m ->
      List.fold_left
        (fun acc (b : Term.branch) ->
          walk (branch_binders ~pointer_fields ~in_place env m.scrutinee b @ env) (Some b.result_type) acc b.body )
        acc m.branches
    | Return _ -> acc
    | Continue c -> ( match passed env c with None -> acc | Some field -> step env c field Release :: acc )
    | Continue_into into -> (
      match passed env into.next with None -> acc | Some field -> recycle env result into field :: acc )
    | Loop _ | Resume _ | Entry _ -> raise Not_walked
  in
  let env =
    List.init n (fun k -> if n - 1 - k = cursor then {cursor = true; pointer_field = None; parts = [Whole]} else unrelated)
  in
  List.rev (walk env None [] l.body)

let plan ~pointer_fields ~in_place (l : Term.loop) =
  let recycles s = match s.action with Recycle _ -> true | Release -> false in
  let walked =
    List.filter_map
      (fun parameter ->
        match steps ~pointer_fields ~in_place l parameter with
        | exception Not_walked -> None
        | steps -> if List.exists recycles steps then Some {parameter; steps} else None )
      (List.init (List.length l.parameters) Fun.id)
  in
  match walked with [c] -> Some c | [] | _ :: _ :: _ -> None

let positioned c positions =
  let at i =
    List.find_map (fun (k, p) -> if Option.equal Int.equal p (Some i) then Some k else None) (List.mapi (fun k p -> (k, p)) positions)
  in
  Option.map
    (fun parameter ->
      { parameter;
        steps =
          List.map
            (fun s -> {s with arguments_read_first = List.filter_map at s.arguments_read_first})
            c.steps } )
    (at c.parameter)

let step_at c turn = List.find_opt (fun s -> Occurrence.equal s.turn turn) c.steps
