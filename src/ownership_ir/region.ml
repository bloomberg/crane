(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** OwnershipIR.  See [ownership_ir.mli]. *)


module Levels = Set.Make (Int)
module Parents = Map.Make (Int)

(* Every read the region holds, in no order. *)
type read = {
  occurrence : Core.Occurrence.t;
  last : bool;  (* nothing after it or beside it reads the variable, or the component it reads *)
  last_whole : bool;  (* nothing after it or beside it reads the variable *)
  consumed : bool;  (* where it stands, its value may be taken *)
}

(* How translation binds a match's pattern variables, where the plan cannot
   tell: a branch generated to rebuild in its scrutinee's storage, named by
   the scrutinee's read and the branch's index, with the constructions that
   may take the storage it frees; and the fields of a record
   taken apart, named by the match itself, which are locals of their own
   where [by_value] says so.  And how it binds a let-bound function with a
   type variable of its own: to a local, at the one instance its uses agree
   on, where the let named by its occurrence is an [Instance] one. *)
type arm =
  | Rebuild of {scrutinee : Core.Occurrence.t; branch : int; consumers : Core.Expr.t list}
  | Fields of {case : Core.Expr.t; by_value : bool list}
  | Instance of Core.Occurrence.t

type resume = {
  calls : Core.Occurrence.t list;
  kept : Core.Binder.t list;
  held : Core.Binder.t list;
  passed : Core.Binder.t list;
}

(* A local fixpoint applied where it is written, [at] its occurrence, and
   what each of its arguments reads: the variables, by level, with their
   parts ([variables]), and every read, by level and occurrence ([read_at]).
   [overlaps] says whether two levels share storage where it stands. *)
type argument = {variables : Levels.t; read_at : (int * Core.Occurrence.t) list}

type entered = {at : Core.Occurrence.t; arguments : argument list; overlaps : int -> int -> bool}

type resumes = {
  origin : Names.GlobRef.t;
  depth : int;
  resume_at : Core.Binder.t -> resume option;
  entry_captures : int option;
  parameter_type : int -> Core.Type.t option;
}

(* Of a let a frame machine resumes at, by its occurrence: each binder the
   frame saved for the call keeps, with its level, and whether the save is
   its last read -- nothing the turn evaluates after the save, the call's
   arguments, nor anything a closure reads at its uses, nor what follows the
   let besides the binders the frame keeps, reads it or a part of it, nor is
   another binder the frame keeps a part of it or it one of that one; and it
   is no variable closures copy. *)
type save = {save_at : Core.Occurrence.t; saved : (Core.Binder.t * int * bool) list}

(* A call that may enter a frame of the machine the region is lowered as
   ({!machine_call}), by its occurrence: what it enters an adopted entry
   with besides its arguments, by level, with whether nothing after the
   call or beside it reads it, and the arguments that are variables, by
   level and read. *)
type entry_read = {call : Core.Occurrence.t; captured : (int * bool) list; arguments : (int * Core.Occurrence.t) list}

(* What a copy of a variable's value is: its bits, a retain of the block it
   points at, or a semantic copy ({!Use}). *)
type copy = Bits | Retain | Duplicate

type t = {
  root : Core.Expr.t;
  n_outer : int;  (* the type variables of the head the region is generated under *)
  outer : int -> Core.Type.t option;
      (* the Core type of a variable bound outside the region, by its index at the root *)
  resumes : resumes option;
  certain : bool;  (* whether the region is lowered as the machine resuming at [resumes] wherever it is generated *)
  root_owned : Levels.t;
  root_copied : Levels.t;  (* variables closures capture a copy of, owned by them alone *)
  arms : arm list;
  reads : read list;
  owned : (Core.Occurrence.t * bool) list;  (* whether the variable a read reads is owned there *)
  read_types : (Core.Occurrence.t * Core.Type.t option) list;
      (* the Core type of the variable a read reads, where known *)
  captures : read list;  (* a lambda's capture of a variable, by the reads inside it *)
  captured_owned : (Core.Occurrence.t * bool) list;
  copied_reads : Core.Occurrence.t list;  (* reads of a variable closures copy *)
  entered : entered list;
  saves : save list;
  saved_owned : (Core.Occurrence.t * Levels.t) list;  (* of each let [saves] names, the levels it keeps owned there *)
  entries : entry_read list;
  entry_owned : (Core.Occurrence.t * Levels.t) list;  (* of each call [entries] names, the levels owned there *)
  effects : Core_plan.Effects.t;  (* the unit's effect operations: a sequential bind runs its continuation inline *)
}

let empty =
  { root = Core.Expr.Erased_value Core.Erasure_reason.Proof;
    n_outer = 0;
    outer = (fun _ -> None);
    resumes = None;
    certain = true;
    root_owned = Levels.empty;
    root_copied = Levels.empty;
    arms = [];
    reads = [];
    owned = [];
    read_types = [];
    captures = [];
    captured_owned = [];
    copied_reads = [];
    entered = [];
    saves = [];
    saved_owned = [];
    entries = [];
    entry_owned = [];
    effects = Core_plan.Effects.empty }

(* The reads in [t] of variables bound outside it, by level, [t] standing [d]
   binders deep. *)
let closure_reads d t =
  let rec go d' acc = function
    | Core.Expr.Bound_variable {index = i; occurrence = o} -> if d' - i < d then (d' - i, o) :: acc else acc
    | Core.Expr.Coerce {value = t; _}
    | Core.Expr.Boxed_value {value = t; _}
    | Core.Expr.Lambda_group_barrier {value = t; _} ->
      go d' acc t
    | Core.Expr.Apply {callee = f; arguments = args} -> List.fold_left (go d') acc (f :: args)
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.fold_left (go d') acc args
    | Core.Expr.Persistent_array {elements = elems; default} ->
      List.fold_left (go d') acc (default :: Array.to_list elems)
    | Core.Expr.Lambda {body = b; _} -> go (d' + 1) acc b
    | Core.Expr.Let {value = a; body = b; _} -> go (d' + 1) (go d' acc a) b
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let fs = Core.Recursion.Group.functions rec_group and defs = Core.Recursion.Group.bodies rec_group in
      Array.fold_left (go (d' + Array.length fs)) acc defs
    | Core.Expr.Match {scrutinee = scrut; branches; _} ->
      Array.fold_left
        (fun acc {Core.Match.Branch.binders = ids; body = body; _} -> go (d' + List.length ids) acc body)
        (go d' acc scrut) branches
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ -> acc
  in
  go d [] t

let worth_moving_ref worth r args =
  if Base.Mapping_plan.is_type_head r then
    (* A typed-mapped type is worth a move unless its copy model makes a copy
       cheap ({!Base.Mapping_plan.copies_cheaply}). *)
    not
      (Base.Mapping_plan.copies_cheaply (Base.Mapping_plan.find r) ~argument:(fun i ->
           match List.nth_opt args i with Some t -> not (worth t) | None -> false))
  else
  (not (Base.Table.is_enum_inductive r))
  && (not (Base.Table.is_coinductive r))
  && ( (not (Base.Table.is_custom r))
     || List.exists worth args
     || not (Base.Table.is_custom_scalar_ref r || Base.Table.is_trivially_copyable_ref r) )

let rec worth_moving = function
  | Core.Type.Global_app {head = r; type_arguments = args; _} -> worth_moving_ref worth_moving r args
  | Core.Type.Arrow _ | Core.Type.Variable _ | Core.Type.Variable_app _ -> true
  (* A type nothing determined, an index a constructor hides, is held in the
     box ([std::any]), which a move hands over. *)
  | Core.Type.Open _ -> true
  | Core.Type.Meta {contents = Some t} -> worth_moving t
  | _ -> false

let rec worth_moving_cpp : type p. p Cpp_ir.Type.t -> bool = function
  | Entity_application (r, tparams, _) -> worth_moving_ref worth_moving_cpp r tparams
  | Foreign {custom; types; _} -> worth_moving_ref worth_moving_cpp custom types
  | Shared_pointer _ | Function _ | Erased _ -> true
  | Variant (_, ts) | Named (_, ts) | External (_, ts) -> List.exists worth_moving_cpp ts
  | Non_deduced t -> worth_moving_cpp t
  | Rebind (h, x) -> worth_moving_cpp h || worth_moving_cpp x
  | Carrier_parameter -> false
  | Reference (Forwarding, t) -> worth_moving_cpp t
  | Type_of _ | Decltype_auto -> false
  | Const t | In_namespace (_, t) | Member (t, _) | Apply (t, _) | Reference (Lvalue, t) -> worth_moving_cpp t
  | Variable _ | Instance _ | Promoted_member _ -> true
  | Decay t -> worth_moving_cpp t
  | Type_constructor _ | Pointer _ | Void | Auto | Any | Obligation _ -> false

(* A value of the global type [r] is a handle on a counted block: a
   coinductive's node, a shared variant's alternative. *)
let shares_ref r = Base.Table.is_coinductive r || Base.Table.is_shared_variant r

(* A typed-mapped type whose copy retains one identity ([RetainIdentity]). *)
let retains_identity r =
  Base.Mapping_plan.is_type_head r
  && (Base.Mapping_plan.find r).copy = Base.Mapping_descriptor.Retain_identity

(* What a copy of a value of the Core type [ty] is: a retain of a block a
   closure or a handle points at, its bits where moving it gains nothing
   ({!worth_moving}) or there is none (an erased value), else a semantic
   copy -- an inductive's value, a mapped type's, one a type variable
   stands for, a box (a type left open, an abstract one the program does
   not see into).  An abbreviation is what it abbreviates; a type
   abstraction erasure removes, what it returns.  [None] of a type
   inference left unsolved, a metavariable or a hole. *)
let rec copy_of_type ty =
  match ty with
  | Core.Type.Meta {contents = Some t} -> copy_of_type t
  | Core.Type.Arrow {parameter = d; result = rest} when Base.Core_util.is_erased_type d -> copy_of_type rest
  | Core.Type.Arrow _ -> Some Retain
  (* An instance of a class is an object of its own, a singleton class's
     too, whatever its method's type. *)
  | Core.Type.Global_app {head = r; _} when Base.Table.is_typeclass r -> Some Duplicate
  | Core.Type.Global_app {head = (Names.GlobRef.ConstRef kn as r); type_arguments = args; _}
    when (not (Base.Table.is_custom r)) && not (Base.Table.is_promoted_type_var r || Base.Table.is_erased_type_const r) -> (
    match Base.Table.lookup_typedef_unchecked kn with
    | Some body -> copy_of_type (Base.Core_util.type_subst_list args body)
    | None -> Some Duplicate )
  | Core.Type.Global_app {head = r; _} when shares_ref r || retains_identity r -> Some Retain
  (* A mapped type's copy copies its arguments: it is its bits only where
     theirs are. *)
  | Core.Type.Global_app {head = r; type_arguments = args; _} ->
    Some (if worth_moving_ref (fun t -> copy_of_type t <> Some Bits) r args then Duplicate else Bits)
  | Core.Type.Variable _ | Core.Type.Variable_app _ | Core.Type.Open _ | Core.Type.String ->
    Some (if worth_moving ty then Duplicate else Bits)
  | Core.Type.Axiom -> Some Duplicate
  | Core.Type.Erased _ -> Some Bits
  (* A type erasure removed -- an existential index, a variable of the
     callee's the scope cannot name, a type computed from a value -- is held
     as a value of its own, in a box or deduced. *)
  | Core.Type.Unknown -> Some Duplicate
  | Core.Type.Meta _ | Core.Type.Hole _ -> None

(* The same, of the C++ type a variable is declared at.  An abbreviation
   the program defines is read as its Core definition: one naming an
   argument as that argument, one of a closure, or with no argument,
   wholly. *)
let rec copy_of_cpp : type p. p Cpp_ir.Type.t -> copy =
 fun ty ->
  match ty with
  | Shared_pointer _ | Function _ -> Retain
  | Entity_application (r, _, _) when shares_ref r || retains_identity r -> Retain
  | Entity_application ((Names.GlobRef.ConstRef kn as r), args, _)
    when (not (Base.Table.is_custom r))
         && (not (Base.Table.is_promoted_type_var r || Base.Table.is_erased_type_const r))
         && Option.has_some (Base.Table.lookup_typedef_unchecked kn) -> (
    let rec body = function Core.Type.Meta {contents = Some t} -> body t | t -> t in
    match body (Option.get (Base.Table.lookup_typedef_unchecked kn)) with
    (* One of its arguments, under another name. *)
    | Core.Type.Variable {variable = j; _} when j >= 1 && j <= List.length args -> copy_of_cpp (List.nth args (j - 1))
    | _ -> (
      match copy_of_type (Core.Type.Global_app {head = r; type_arguments = []; index_arguments = []}) with
      | Some Retain -> Retain
      | Some c when args = [] -> c
      | Some _ | None -> if worth_moving_cpp ty then Duplicate else Bits ) )
  | Entity_application (r, args, _) ->
    if worth_moving_ref (fun t -> copy_of_cpp t <> Bits) r args then Duplicate else Bits
  | Foreign {custom; types; _} ->
    if worth_moving_ref (fun t -> copy_of_cpp t <> Bits) custom types then Duplicate else Bits
  (* A box holds a value of its own, which a copy copies. *)
  | Any | Obligation Opaque_type -> Duplicate
  | Const t | In_namespace (_, t) | Reference (_, t) | Non_deduced t -> copy_of_cpp t
  | _ -> if worth_moving_cpp ty then Duplicate else Bits

(* A variable is named by its de Bruijn level in the region: the number of
   binders around its binding site, counted from the region's root, so that
   one the region does not bind has a negative level.  [parents] maps a
   pattern variable to the variable its match took apart.

   A component of a pair variable read through its projection mapping is a
   part of it too, named by a level of its own below every variable's: the
   [first] and [second] components of the variable at [base] are [component
   base 0] and [component base 1].  Being a part of [base] without being a
   binder, it is in scope exactly where [base] is. *)

let component_floor = -(1 lsl 50)
let component base field = component_floor + ((base + (1 lsl 30)) * 2) + field
let component_base l = if l < component_floor / 2 then Some (((l - component_floor) / 2) - (1 lsl 30)) else None

(* The variable a level names storage of: a component's pair, or itself. *)
let storage l = match component_base l with Some base -> base | None -> l

let rec ancestors parents l =
  match component_base l with
  | Some base -> base :: ancestors parents base
  | None -> (
    match Parents.find_opt l parents with Some p -> p :: ancestors parents p | None -> [])

(* Two variables share storage when one is the other, or a part of it. *)
let overlap parents l m = l = m || List.mem m (ancestors parents l) || List.mem l (ancestors parents m)

(* The variables of [s] seen from [d] binders deep, leaving the scope of the
   binders at [d] and deeper: a part stays a read of the nearest variable it
   is a part of that is still in scope, anything else is dropped. *)
let leave parents d s =
  Levels.filter_map
    (fun l ->
      if storage l < d then Some l else List.find_opt (fun p -> p < d) (ancestors parents l) )
    s

(* The component of the pair variable [Core.Expr.Bound_variable i] that [r] applied to it reads,
   [t] standing [d] binders deep: [r] is an inline custom spelled as the
   projection of its argument's [first] or [second] member. *)
let projected d r t =
  match (Base.Table.inline_custom_text r, t) with
  | Some s, Core.Expr.Bound_variable {index = i; occurrence = o} when Base.Table.is_inline_custom r -> (
    match Cpp_ir.Foreign_template.pair_projection_field s with
    | Some "first" -> Some (component (d - i) 0, o)
    | Some "second" -> Some (component (d - i) 1, o)
    | _ -> None )
  | _ -> None

let rec strip =
  function Core.Expr.Coerce {value = t; _} | Core.Expr.Boxed_value {value = t; _}
    | Core.Expr.Lambda_group_barrier {value = t; _} -> strip t | t -> t

(* Whether the custom match [branches] binds the pattern variable [j] of its
   branch [k] as a variable of its own, a copy rather than a part of the
   scrutinee: its template declares it by value. *)
let copied_binder branches k j =
  Base.Table.is_custom_match branches
  && Cpp_ir.Foreign_template.declared_by_value (Base.Table.find_custom_match branches) k j

(* What the pattern variables of a match's branch [k] are parts of: the
   variable it matches, when it matches one, unless the branch binds the
   variable as a copy of its own ({!copied_binder}). *)
let bind_parts ?(k = 0) ?(branches = [||]) parents d ~n scrut =
  let rec go parents l =
    if l >= d + n then parents
    else
      let parents =
        match strip scrut with
        | Core.Expr.Bound_variable {index = i; _} when not (copied_binder branches k (l - d)) ->
          Parents.add l (d - i) parents
        | _ -> Parents.remove l parents
      in
      go parents (l + 1)
  in
  go parents d

let bind parents d ~n =
  let rec go parents l = if l >= d + n then parents else go (Parents.remove l parents) (l + 1) in
  go parents d

(* The variables bound outside [t] that [t] reads, [t] standing [d] binders
   deep: the components it reads of a pair, or, under a closure, which
   copies what it captures whole, the pair.  A variable at a level of
   [outside] is counted only where a closure reads it: a variable closures
   copy is read outside them in the original. *)
let rec free ?(parts = true) ?(outside = Levels.empty) parents d t =
  let closure_frees = frees ~parts and closure_under = under ~parts in
  let free = free ~parts ~outside and frees = frees ~parts ~outside and under = under ~parts ~outside in
  match t with
  | Core.Expr.Bound_variable {index = i; _} ->
    if i > 0 && not (Levels.mem (d - i) outside) then Levels.singleton (d - i) else Levels.empty
  | Core.Expr.Coerce {value = t; _}
  | Core.Expr.Boxed_value {value = t; _}
  | Core.Expr.Lambda_group_barrier {value = t; _} ->
    free parents d t
  | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _};
                     arguments = [arg]} when parts && projected d r (strip arg) <> None ->
    Levels.singleton (fst (Option.get (projected d r (strip arg))))
  | Core.Expr.Apply {callee = f; arguments = args} -> frees parents d (f :: args)
  | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> frees parents d args
  | Core.Expr.Persistent_array {elements = elems; default} -> frees parents d (default :: Array.to_list elems)
  | Core.Expr.Lambda {body; _} -> whole (closure_under parents d ~n:1 body)
  | Core.Expr.Let {value = a; body = b; _} -> Levels.union (free parents d a) (under parents d ~n:1 b)
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let fs = Core.Recursion.Group.functions rec_group and defs = Core.Recursion.Group.bodies rec_group in
    let n = Array.length fs in
    let parents' = bind parents d ~n in
    whole (leave parents' d (closure_frees parents' (d + n) (Array.to_list defs)))
  | Core.Expr.Match {scrutinee = scrut; branches; _} ->
    let k = ref (-1) in
    Array.fold_left
      (fun acc {Core.Match.Branch.binders = ids; body = body; _} ->
        incr k;
        let n = List.length ids in
        let parents' = bind_parts ~k:!k ~branches parents d ~n scrut in
        Levels.union acc (leave parents' d (free parents' (d + n) body)) )
      (free parents d scrut) branches
  | Core.Expr.Global _
  | Core.Expr.Runtime_error _
  | Core.Expr.Erased_value _
  | Core.Expr.Axiom_value _
  | Core.Expr.UInt63 _
  | Core.Expr.Numeral _
  | Core.Expr.Float64 _
  | Core.Expr.String _ ->
    Levels.empty

and frees ?parts ?outside parents d ts =
  List.fold_left (fun acc t -> Levels.union acc (free ?parts ?outside parents d t)) Levels.empty ts

and under ?parts ?outside parents d ~n body =
  let parents' = bind parents d ~n in
  leave parents' d (free ?parts ?outside parents' (d + n) body)

(* What a closure reading [s] captures: every component it reads is read
   whole. *)
and whole s = Levels.map storage s

(* Whether a let binds the closure [a] to a C++ local, under a head of
   [n_outer] type variables: one with a type variable of its own is lifted to
   a function template, or inlined at its uses, instead. *)
let closure_local ~n_outer ty a =
  match a with
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group in
    not (Base.Type_util.own_type_variables ~n_outer (List.map snd (Array.to_list ids)))
  | Core.Expr.Lambda _ -> not (Base.Type_util.own_type_variables ~n_outer [ty])
  | _ -> false

let at_instance arms occurrence =
  List.exists (function Instance o -> Core.Occurrence.equal o occurrence | Rebuild _ | Fields _ -> false) arms

(* Whether the closure a let binds may read what it closes over at its uses
   rather than where it is made: a local fixpoint closes over its
   surroundings by reference, and a lambda with a type variable of its own
   may be lifted to a function template, to which each use passes them, or
   inlined at each use.  A lambda bound to a local, an [Instance] one
   included, is a value holding copies. *)
let reads_at_uses ~n_outer ~arms ty a occurrence =
  match strip a with
  | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ -> true
  | Core.Expr.Lambda _ -> Base.Type_util.own_type_variables ~n_outer [ty] && not (at_instance arms occurrence)
  | _ -> false

(* A record's field read out of it, by its projection or by the match
   taking the record apart that returns one field: the record read. *)
let field_of = function
  | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; arguments = [t]} when Base.Table.is_projection r -> Some t
  | Core.Expr.Match {scrutinee_type = ty;
                     scrutinee = t;
                     branches = [|{Core.Match.Branch.binders = ids;
                                   body = Core.Expr.Bound_variable {index = k; _}; _}|]; _}
    when Base.Table.record_fields_of_type ty <> [] && k <= List.length ids ->
    Some t
  | _ -> None

(* Whether translation spells [t] as often as it is mentioned, being a
   variable or a record field of one. *)
let rec spelled_in_place = function
  | Core.Expr.Bound_variable _ -> true
  | Core.Expr.Coerce {value = t; _}
  | Core.Expr.Boxed_value {value = t; _}
  | Core.Expr.Lambda_group_barrier {value = t; _} ->
    spelled_in_place t
  | t -> ( match field_of t with Some t -> spelled_in_place t | None -> false )

(* Whether a match may take its scrutinee's value, as translation generates
   it.  A variant's alternatives are bound by reference into the scrutinee,
   which a variable that is matched keeps; a custom match whose template
   spells the scrutinee twice reads a variable or a field of one in place,
   and evaluates anything else once into a temporary.  An enum is a value,
   a record's fields are read one at a time, and any other custom match
   evaluates its scrutinee once. *)
let scrutinee_consumed ty scrut branches =
  match Core_plan.Match_kind.classify ty branches with
  | Custom ->
    let uses =
      List.length
        (List.filter (( = ) Cpp_ir.Foreign_template.Scrut)
           (Cpp_ir.Foreign_template.match_template (Base.Table.find_custom_match branches)) )
    in
    uses <= 1 || not (spelled_in_place scrut)
  | Record _ -> true
  | Variant ->
    Array.for_all
      (fun {Core.Match.Branch.pattern = pat; _} ->
        match pat with
        | Core.Pattern.Constructor {constructor = Names.GlobRef.ConstructRef (ip, _); _} ->
          Base.Table.is_enum_inductive (Names.GlobRef.IndRef ip)
        | _ -> true )
      branches

(* How many times an argument of [r] is evaluated: an inline custom splices
   it as often as its template names it, and an operation mapping evaluates
   each argument once, into a slot its template reads
   ({!Cpp_passes.Shared_args}). *)
let evaluations r =
  if Base.Table.is_mapped_operation r then fun _ -> 1
  else
  match Base.Table.inline_custom_text r with
  | Some s when Base.Table.is_inline_custom r -> Cpp_ir.Foreign_template.arg_mentions s
  | _ -> fun _ -> 1

(* Whether argument [k] of [r] is only borrowed for the call: an operation
   mapping's argument it does not own ({!Base.Mapping_operation.owns}) --
   read, written in place or ignored -- is never moved into it. *)
let borrowed_by r =
  if Base.Table.is_mapped_operation r then
    let owned = Base.Mapping_operation.owned_call_arguments (Base.Mapping_operation.find r) in
    fun k -> not (Option.default true (List.nth_opt owned k))
  else fun _ -> false

let sequential_bind effects use = Core_plan.Effects.lookup effects use = Some {operation = Bind; mode = Sequential}

(* What an application, perhaps applied in turn, applies: through casts. *)
let rec call_head f = match strip f with Core.Expr.Apply {callee = g; _} -> call_head g | h -> h

(* The call [a] makes, by its occurrence, where it is one -- of a global, of
   a local fixpoint's member, or a local fixpoint applied where it is
   written -- applied in one application or several. *)
let call_of a =
  match strip a with
  | Core.Expr.Apply {callee = f; _} -> (
    match call_head f with
    | Core.Expr.Global {occurrence; _}
    | Core.Expr.Bound_variable {occurrence; _}
    | Core.Expr.Fixpoint {occurrence; _}
    | Core.Expr.Cofixpoint {occurrence; _} ->
      Some occurrence
    | _ -> None )
  | _ -> None

(* Whether the branches of a match on a value of type [ty] are where the
   value of the match is bound, rather than in a closure run in its place
   (as {!Core_plan.Recursion} reads a right-hand side ending in its branches). *)
let bound_in_place ty branches = Core_plan.Match_kind.bound_in_place (Core_plan.Match_kind.classify ty branches)

(* The calls [a] ends in: the call it is, or those the branches of a match
   bound in place end in, through lets and casts. *)
let rec ending_calls a =
  match (call_of a, strip a) with
  | Some call, _ -> [call]
  | None, Core.Expr.Match {scrutinee_type = ty; branches; _} when bound_in_place ty branches ->
    List.concat_map (fun {Core.Match.Branch.body = b; _} -> ending_calls b) (Array.to_list branches)
  | None, Core.Expr.Let {body = b; _} -> ending_calls b
  | None, _ -> []

(* The variables, by level, that a frame keeps across the calls [a] ends
   in, [let _ := a in _] at [occurrence] standing [d] binders deep: where
   the let is a point a frame machine resumes at, the frame saving them is
   made before such a call's arguments are evaluated, and what follows
   reads them in the frame.  The save reads them: what reads them before it
   does not read them last. *)
let resume_of resumes d a occurrence =
  match (resumes, ending_calls a) with
  | Some _, [] | None, _ -> None
  | Some {origin; depth; resume_at; _}, ending -> (
    match resume_at (Core.Binder.make ~origin ~level:(depth + d) ~site:(Binding occurrence) ()) with
    | Some ({calls; _} as r) when List.exists (fun c -> List.exists (Core.Occurrence.equal c) calls) ending ->
      Some (depth, r)
    | Some _ | None -> None )

let kept_binders resumes d a occurrence =
  match resume_of resumes d a occurrence with
  | Some (depth, {kept; _}) -> List.map (fun (b : Core.Binder.t) -> (b, b.level - depth)) kept
  | None -> []

let kept_across resumes d a occurrence = Levels.of_list (List.map snd (kept_binders resumes d a occurrence))

(* Of the binders the frame saved at such a let keeps, the levels of those
   it holds itself ({!resume.held}). *)
let held_across resumes d a occurrence =
  match resume_of resumes d a occurrence with
  | Some (depth, {held; _}) -> Levels.of_list (List.map (fun (b : Core.Binder.t) -> b.level - depth) held)
  | None -> Levels.empty

(* Of those, the levels of the ones the frame may keep as pointers
   ({!resume.passed}). *)
let passed_across resumes d a occurrence =
  match resume_of resumes d a occurrence with
  | Some (depth, {passed; _}) -> Levels.of_list (List.map (fun (b : Core.Binder.t) -> b.level - depth) passed)
  | None -> Levels.empty

(* A call [f] applied [d] deep makes that may enter a frame of the machine
   the region is lowered as, by its occurrence, and what it enters with
   besides its arguments: a call of the definition itself, or of a local
   function -- the member of the fixpoint whose body the region is, an
   adopted entry entered with the fixpoint's captures, [`Member] -- or a
   local fixpoint applied where it is written, entered with what it
   captures, [`Fixpoint]. *)
let machine_call resumes d f =
  match resumes with
  | None -> None
  | Some {origin; entry_captures; _} -> (
    match strip f with
    | Core.Expr.Fixpoint {occurrence = at; _} | Core.Expr.Cofixpoint {occurrence = at; _} -> Some (at, `Fixpoint)
    | _ -> (
      match (call_head f, entry_captures) with
      | Core.Expr.Global {callee; occurrence; _}, _ when Base.Common.globref_equal callee origin -> Some (occurrence, `Plain)
      | Core.Expr.Bound_variable {index = i; occurrence}, Some k when d - i = -k -> Some (occurrence, `Member)
      | Core.Expr.Bound_variable {occurrence; _}, _ -> Some (occurrence, `Plain)
      | _ -> None ) )

(* A frame saved where the right-hand side of the let at [let_at] ends in one of
   the calls [calls]: the binders it keeps, with their levels, and what is
   read once the let is done. *)
type tail_save = {
  let_at : Core.Occurrence.t;
  calls : Core.Occurrence.t list;
  kept_at : (Core.Binder.t * int) list;
  kept : Levels.t;
  outside : Levels.t;
}

(* The reads of [t], each with whether it is a last use, the captures of
   the closures it makes, the local fixpoints it applies where they are
   written, the saves of the machine it may be lowered as, and the calls
   entering that machine's entries: one backward walk, from what is live
   after each subterm to what is live before it. *)
let liveness ~effects ~n_outer ~copied ~arms ~resumes t =
  (* The captures a call re-entering the entry the region is lowered as
     passes it, and the level of the fixpoint's member such a call names. *)
  let entry_captures =
    match resumes with
    | Some {entry_captures = Some k; _} -> Some (-k, lazy (Levels.filter (fun l -> l < -k) (free Parents.empty 0 t)))
    | Some _ | None -> None
  in
  let reads = ref [] in
  let captures = ref [] in
  let entered = ref [] in
  let saves = ref [] in
  let entries = ref [] in
  (* The call at [call] entering an entry with [args], passing [captured]
     besides them, [live] read after it, [d] deep. *)
  let enters call captured args ~pinned parents d live =
    let after =
      List.fold_left (fun acc a -> Levels.union acc (free ~outside:copied parents d a))
        (Levels.union live pinned) args in
    let last l = (not (Levels.mem l copied)) && not (Levels.exists (overlap parents l) after) in
    entries :=
      { call;
        captured = List.map (fun l -> (l, last l)) (Levels.elements captured);
        arguments = List.filter_map
          (fun a -> match strip a with Core.Expr.Bound_variable {index = i; occurrence = o} ->
            Some (d - i, o) | _ -> None) args }
      :: !entries
  in
  (* [walk ~consumed ~pinned parents d live t] records [t]'s reads and is
     what is live before [t], given [live] after it: both sets of variables
     in scope at [t], [d] binders deep.  [consumed] is whether [t] stands
     where its value may be taken.  It describes [t]'s own position: a
     subterm whose value is [t]'s -- a cast's operand, a let's body, a
     branch -- stands where [t] does, and any other takes its value, unless
     it is read in place. *)
  let rec walk ?(consumed = true) ?tail ~pinned parents d live t =
    let read l occurrence =
      let last_of m = not (Levels.exists (overlap parents m) (Levels.union live pinned)) in
      reads := {occurrence; last = last_of l; last_whole = last_of (storage l); consumed} :: !reads;
      (* Of a variable closures copy, a read outside them reads the original,
         not the copy. *)
      if Levels.mem (storage l) copied then live else Levels.add l live
    in
    match t with
    (* A call a frame is saved for, where the right-hand side of the let
       the machine resumes at ends in it: the save is made before its
       arguments are evaluated. *)
    | _
      when Option.cata
        (fun s -> Option.cata (fun c -> List.exists (Core.Occurrence.equal c) s.calls) false (call_of t)) false tail
      ->
      let s = Option.get tail in
      let saved, after_save = Levels.partition (fun l -> Levels.mem (storage l) s.kept) live in
      (* A call re-entering the entry the region is lowered as -- of the
         fixpoint's member -- passes the entry the fixpoint's captures as
         well. *)
      let entered =
        match (entry_captures, strip t) with
        | Some (member, captures), Core.Expr.Apply {callee = f; _} -> (
          match call_head f with Core.Expr.Bound_variable {index = i; _} when d - i = member -> Lazy.force captures
            | _ -> Levels.empty )
        | _ -> Levels.empty
      in
      (* What follows the let reads a binder the frame keeps in the frame
         ({!resume.kept}), there or in a handler further on: the let's
         binder may be an argument, [sz0 (let r := g m in sz1 r)], and what
         reads [sz0] after the let is the same handler. *)
      let read_after = Levels.union (free parents d t) (Levels.union (Levels.diff s.outside s.kept) entered) in
      (* A part the frame keeps beside its whole is saved before the whole
         ({!Control_to_cpp.Frame}): the whole may still be moved in after it,
         but not a part while its whole is kept. *)
      let last l =
        (not (Levels.mem l copied))
        && (not (Levels.exists (overlap parents l) read_after))
        && not
             (Levels.exists
                (fun m -> overlap parents l m && not (List.mem l (ancestors parents m)))
                (Levels.remove l s.kept))
      in
      saves := {save_at = s.let_at; saved = List.map (fun (b, l) -> (b, l, last l)) s.kept_at} :: !saves;
      Levels.union saved (walk ~consumed ~pinned parents d after_save t)
    | Core.Expr.Bound_variable {index = i; occurrence} -> read (d - i) occurrence
    | Core.Expr.Coerce {value = t; _}
    | Core.Expr.Boxed_value {value = t; _}
    | Core.Expr.Lambda_group_barrier {value = t; _} ->
      walk ~consumed ?tail ~pinned parents d live t
    (* A component read through its projection is a part of the pair: a read
       of the other component is not a later read of it. *)
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _};
                       arguments = [arg]} when projected d r (strip arg) <> None ->
      let l, occurrence = Option.get (projected d r (strip arg)) in
      read l occurrence
    (* A field is read out of its record where the projection stands. *)
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; arguments = [arg]} when Base.Table.is_projection r ->
      walk ~consumed ~pinned parents d live arg
    | Core.Expr.Match {scrutinee = scrut; _} when field_of t <> None -> walk ~consumed ~pinned parents d live scrut
    (* A bind generated as sequencing runs its action and then its
       continuation's body, inline, though a mapping spells the same bind as
       an inline custom where it is generated as a call. *)
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = (_ :: _ :: _ as args)}
      when sequential_bind effects use -> (
      let action, k = Base.Common.last_two args in
      match Base.Core_util.collect_lams k with
      | [], _ -> walk ~pinned parents d (walk ~consumed:false ~pinned parents d live k) action
      | ids, body ->
        let n = List.length ids in
        let parents' = bind parents d ~n in
        let parents' = after_resume parents' d action use.occurrence in
        let live_body = walk ~consumed ?tail ~pinned parents' (d + n) live body in
        walk ?tail:(saved_at d action use.occurrence ~outside:(Levels.union live pinned)) ~pinned parents d
          (leave parents' d live_body) action )
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; arguments = args} when Base.Table.is_inline_custom r ->
      unsequenced ~evaluated:(evaluations r) ~inspected:(borrowed_by r) ~pinned parents d live args
    (* A local fixpoint applied where it is written binds its parameters to
       its arguments in order: each is followed by the later ones alone, and
       by what the fixpoint reads, which it reads as it runs, after them all.
       What it copies, it copies before any of them is evaluated. *)
    | Core.Expr.Apply
      {callee = (Core.Expr.Fixpoint {occurrence = at; _} | Core.Expr.Cofixpoint {occurrence = at; _} as f);
                       arguments = args} ->
      (* A machine adopting the fixpoint enters it here with what it
         captures. *)
      if Option.has_some (machine_call resumes d f) then enters at (free parents d f) args ~pinned parents d live;
      let reads_of = List.map (free ~outside:copied parents d) args in
      ignore (walk ~consumed:false ~pinned parents d (List.fold_left Levels.union live reads_of) f);
      entered :=
        { at;
          overlaps = overlap parents;
          arguments = List.map2 (fun t variables -> {variables; read_at = closure_reads d t}) args reads_of }
        :: !entered;
      List.fold_right (fun t live -> walk ~pinned parents d live t) args (Levels.union live (free parents d f))
    (* A function is called through: [std::move(f)(x)] still calls [f]. *)
    | Core.Expr.Apply {callee = f; arguments = args} ->
      ( match (machine_call resumes d f, entry_captures) with
      | Some (call, `Member), Some (_, captures) -> enters call (Lazy.force captures) args ~pinned parents d live
      | Some (call, (`Member | `Plain | `Fixpoint)), _
        when List.exists (fun a -> match strip a with Core.Expr.Bound_variable _ -> true | _ -> false) args ->
        enters call Levels.empty args ~pinned parents d live
      | _ -> () );
      unsequenced ~inspected:(fun k -> k = 0) ~pinned parents d live (f :: args)
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> unsequenced ~pinned parents d live args
    | Core.Expr.Persistent_array {elements = elems; default} ->
      unsequenced ~pinned parents d live (default :: Array.to_list elems)
    (* A closure reads what it closes over where it is made; its own body
       is a region of its own. *)
    | Core.Expr.Lambda _ | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ ->
      let captured = free parents d t in
      (* A lambda copies what it captures when it is made, all at once; so
         does a local fixpoint generated as closures, though one generated
         by reference refers to it instead and is given no capture moves. *)
      List.iter
        (fun (l, occurrence) ->
          let shared = Levels.exists (overlap parents l) in
          let last = not (shared live || shared pinned || shared (Levels.remove l captured)) in
          captures := {occurrence; last; last_whole = last; consumed = true} :: !captures )
        (closure_reads d t);
      Levels.union live captured
    | Core.Expr.Let {binder_type = ty; value = a; body = b; occurrence; _} ->
      let pinned_b =
        if reads_at_uses ~n_outer ~arms ty a occurrence then Levels.union pinned (free parents d a) else pinned in
      let parents_b = after_resume (bind parents d ~n:1) d a occurrence in
      let live_b = walk ~consumed ?tail ~pinned:pinned_b parents_b (d + 1) live b in
      walk ?tail:(saved_at d a occurrence ~outside:(Levels.union live pinned)) ~pinned parents d
        (leave parents_b d live_b) a
    (* A branch reads its pattern variables through the scrutinee's own
       evaluation -- a field of the record it names, a component of the pair
       it hands over -- so what follows the scrutinee is what the branches
       read besides them. *)
    | Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches; _} ->
      let k = ref (-1) in
      let after_scrut =
        Array.fold_left
          (fun acc {Core.Match.Branch.binders = ids; body = body; _} ->
            incr k;
            let n = List.length ids in
            let tail = if bound_in_place ty branches then tail else None in
            let live_body =
              walk ~consumed ?tail ~pinned (bind_parts ~k:!k ~branches parents d ~n scrut) (d + n) live body
            in
            Levels.union acc (leave (bind parents d ~n) d live_body) )
          Levels.empty branches
      in
      walk
        ~consumed:(scrutinee_consumed ty scrut branches)
        ~pinned parents d after_scrut scrut
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ -> live
  (* What follows a resume at the binder [a] binds at [occurrence], [d]
     deep, reads each binder the frame holds itself in a field of its own, a
     part of no other. *)
  and after_resume parents d a occurrence =
    List.fold_left (fun parents l -> Parents.remove l parents) parents
      (Levels.elements (held_across resumes d a occurrence))
  (* The frame saved where [a], bound at [occurrence], [d] deep, ends in a
     call the point resumes after: at each such call, [outside] read once
     the binding is done. *)
  and saved_at d a occurrence ~outside =
    match (kept_binders resumes d a occurrence, resume_of resumes d a occurrence) with
    | (_ :: _ as kept_at), Some (_, r) ->
      Some {let_at = occurrence; calls = r.calls; kept_at; kept = Levels.of_list (List.map snd kept_at); outside}
    | _ -> None
  (* The terms of [ts] are evaluated in no fixed order: each is followed by
     whatever the others read, and by what it reads itself when it is
     evaluated twice.  One evaluated not at all reads nothing; one
     [inspected] is read in place. *)
  and unsequenced ?(evaluated = fun _ -> 1) ?(inspected = fun _ -> false) ~pinned parents d live ts =
    (* A lone term evaluated once is followed by no other term's reads, so
       what it reads itself -- a whole subterm's free variables, at every
       level of a nest of one-argument constructions -- is not worked out. *)
    let reads_of = lazy (List.map (free ~outside:copied parents d) ts) in
    let lone = match ts with [_] -> true | _ -> false in
    List.mapi
      (fun k t ->
        match evaluated k with
        | 0 -> live
        | m ->
          let others =
            if lone && m = 1 then [] else List.filteri (fun j _ -> j <> k || m > 1) (Lazy.force reads_of)
          in
          walk ~consumed:(not (inspected k)) ~pinned parents d (List.fold_left Levels.union live others) t )
      ts
    |> List.fold_left Levels.union live
  in
  ignore (walk ~pinned:Levels.empty Parents.empty 0 Levels.empty t);
  (!reads, !captures, !entered, !saves, !entries)

type fate = Last_use | Read_again | Inspected | Unplanned

let fate_in ?(whole = false) reads o =
  match List.filter (fun r -> Core.Occurrence.equal o r.occurrence) reads with
  | [] -> Unplanned
  | copies ->
    if not (List.for_all (fun r -> if whole then r.last_whole else r.last) copies) then Read_again
    else if List.for_all (fun r -> r.consumed) copies then Last_use
    else Inspected

let fate ?whole p o = fate_in ?whole p.reads o

(* The inductive a match's branches take apart, if one names a constructor. *)
let matched_inductive branches =
  Array.fold_left
    (fun acc {Core.Match.Branch.pattern = pat; _} ->
      match (acc, pat) with
      | None, Core.Pattern.Constructor {constructor = Names.GlobRef.ConstructRef (ip, _); _} ->
        Some (Names.GlobRef.IndRef ip)
      | _ -> acc )
    None branches

(* The variable whose storage a match reads its fields out of: through a
   magic cast, and through the application that instantiates a binder of
   dependent type at its witness.  Only a scrutinee that is the variable
   itself is taken apart as a value the region owns; one named through an
   application is read in place. *)
let rec scrutinee_storage = function
  | Core.Expr.Bound_variable {index = i; occurrence = o} -> Some (i, o)
  | Core.Expr.Coerce {value = t; _}
  | Core.Expr.Boxed_value {value = t; _}
  | Core.Expr.Lambda_group_barrier {value = t; _}
  | Core.Expr.Apply {callee = t; _} ->
    scrutinee_storage t
  | _ -> None

let scrutinee_var scrut = match strip scrut with Core.Expr.Bound_variable {index = i;
                                                                           occurrence = o} -> Some (i, o) | _ -> None

(* The binding modes a region's lowering gives its binders, as functions of
   whether a read's variable is owned where it is read ([owned]) and of the
   read's fate ([fate]). *)
module Binding = struct
  (* A custom match takes a pair apart by value when its template is a
     structured binding, which may bind either way, and it is the pair's last
     reader: a pair the scrutinee has just built, or a variable owned there
     that the branch does not read whole. *)
  let pair_by_value ~owned scrut branches =
    Array.length branches = 1
    && (match matched_inductive branches with
       | Some r -> Base.Type_util.is_prod_global r
       | None -> false )
    && Base.Table.is_custom_match branches
    && Cpp_ir.Foreign_template.structured_binding (Base.Table.find_custom_match branches) <> None
    &&
    match scrutinee_var scrut with
    | Some (i, o) ->
      let {Core.Match.Branch.binders = ids; body = body; _} = branches.(0) in
      owned i o && Core_plan.Escape.nb_occur_match (i + List.length ids) body = 0
    | None -> true

  (* A let binds by reference the field it projects out of a record that is
     not moved there. *)
  (* Or the component a mapped operation returns as a canonical borrow of
     its argument ([fst p] is [p.first]), worth a copy, out of a variable
     the region does not own: a component stored in place moves with its
     owner, so the owner must be one nothing here moves from. *)
  let projects_in_place ~owned ~fate ty a =
    match a with
    | Core.Expr.Match {scrutinee = Core.Expr.Bound_variable {index = k; occurrence = o};
                       branches = [|{Core.Match.Branch.body = Core.Expr.Bound_variable _; _}|]; _} ->
      Core_plan.Escape.is_shared_ptr_type ty && not (owned k o && fate o = Last_use)
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = g; _}; arguments = args}
      when Base.Table.is_mapped_operation g -> (
      worth_moving ty
      &&
      match Base.Mapping_operation.canonical_borrow_origin (Base.Mapping_operation.find g) with
      | Some i -> (
        match List.nth_opt args i with
        | Some (Core.Expr.Bound_variable {index = k; occurrence = o}) -> not (owned k o)
        | _ -> false )
      | None -> false )
    | _ -> false

  (* A variant match takes apart a scrutinee the region owns, binding its
     fields by mutable reference, where nothing after the match reads the
     variable: what is taken apart, or recycled, is gone for a later read. *)
  let owns_scrutinee ~owned ~fate scrut =
    match scrutinee_var scrut with
    | Some (i, o) -> owned i o && (match fate o with Read_again -> false | Last_use | Inspected | Unplanned -> true)
    | None -> false
end

(* [ownership ~reads ~arms ~owned t] says, of every read in [t], whether the
   variable it reads is owned where it is read: bound by value, so that the
   region may take its value.  [owned] holds the levels of the variables the
   region owns at its root. *)
let ownership ~effects ~n_outer ~outer ~resumes ~certain ~reads ~arms ~owned ~copied t =
  let out = ref [] in
  let read_types = ref [] in
  let captured = ref [] in
  let copied_reads = ref [] in
  let saved_owned = ref [] in
  let entry_owned = ref [] in
  (* The levels of the binders the frames of the turn [own] is in hold
     ({!resume.held}). *)
  let frame_held = ref Levels.empty in
  (* The pattern variables in scope bound to a variant's field stored
     behind a pointer: a copy of one is a handle to a node others may
     share. *)
  let handles = ref Levels.empty in
  (* The Core types of the binders by level: those the region binds as the
     walk reaches them, the machine's parameters as {!resumes} gives them. *)
  let types = Hashtbl.create 16 in
  let bound d ty = Hashtbl.replace types d ty in
  let binder_type l =
    if l >= 0 then Hashtbl.find_opt types l
    else match resumes with Some r -> r.parameter_type (r.depth + l) | None -> None
  in
  (* Where the type of a variable bound outside the region is not a loop
     parameter's, it is the one its scope gives it. *)
  let read_type l = match binder_type l with Some ty -> Some ty | None -> if l < 0 then outer (-l) else None in
  (* What follows a resume the machine certainly makes owns each binder its
     frame holds by value: one the region binds, or a parameter -- not an
     adopted entry's capture, which may be such a field bound outside it,
     nor a method's receiver, which the frame points at, nor one the frame
     may keep as a pointer ({!resume.passed}).  With the levels it owns so
     and did not before. *)
  let after_resume owned d a occurrence =
    let own_binder l =
      Option.cata worth_moving false (binder_type l)
      && (not (Levels.mem l !handles))
      && (not (Levels.mem l copied))
      && (not (Levels.mem l (passed_across resumes d a occurrence)))
      && match resumes with Some {entry_captures = Some k; _} -> l > -k | Some _ | None -> true
    in
    if certain then
      let added = Levels.diff (Levels.filter own_binder (held_across resumes d a occurrence)) owned in
      (Levels.union owned added, added)
    else (owned, Levels.empty)
  in
  (* The levels owned only as what follows a resume ({!after_resume}). *)
  let resumed = ref Levels.empty in
  let resuming added f =
    let enclosing = !resumed in
    resumed := Levels.union enclosing added;
    f ();
    resumed := enclosing
  in
  (* The frame of the entry the region is lowered as holds what it reads
     from outside it, its parameters and its captures, from its root on. *)
  let outer =
    match resumes with
    | Some {entry_captures = Some _; _} -> Levels.filter (fun l -> l < 0) (free Parents.empty 0 t)
    | Some _ | None -> Levels.empty
  in
  let frame_held_now () = Levels.union !frame_held outer in
  let rec own owned d t =
    let all = List.iter (own owned d) in
    match t with
    | Core.Expr.Bound_variable {index = i; occurrence} ->
      out := (occurrence, Levels.mem (d - i) owned) :: !out;
      read_types := (occurrence, read_type (d - i)) :: !read_types;
      if Levels.mem (d - i) copied then copied_reads := occurrence :: !copied_reads
    | Core.Expr.Coerce {value = t; _}
    | Core.Expr.Boxed_value {value = t; _}
    | Core.Expr.Lambda_group_barrier {value = t; _} ->
      own owned d t
    (* A bind generated as sequencing binds its continuation's parameter to
       the action's value. *)
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = (_ :: _ :: _ as args)}
      when sequential_bind effects use -> (
      let action, k = Base.Common.last_two args in
      own owned d action;
      match Base.Core_util.collect_lams k with
      | [], _ -> own owned d k
      | ((_, ty) :: _ as ids), body ->
        let n = List.length ids in
        List.iteri (fun j (_, ty) -> bound (d + n - 1 - j) ty) ids;
        let owned_k, added = after_resume owned d action use.occurrence in
        saving d action use.occurrence owned (fun () ->
            resuming added (fun () ->
                own (if worth_moving ty then Levels.add (d + n - 1) owned_k else owned_k) (d + n) body ) ) )
    | Core.Expr.Apply {callee = f; arguments = args} ->
      let entered = entering d f in
      Option.iter (fun call -> entry_owned := (call, Levels.union owned (frame_held_now ())) :: !entry_owned) entered;
      (* A function the region is handed -- a variable bound outside it, not
         the member of the fixpoint whose body it is -- is passed its
         arguments as it would be with no resume: taking one by move would
         change the signature its parameter requires of it. *)
      let handed =
        match (machine_call resumes d f, call_head f) with
        | Some (_, `Member), _ -> false
        | _, Core.Expr.Bound_variable {index = i; _} -> d - i < 0
        | _ -> false
      in
      if handed then begin
        own owned d f;
        List.iter (own (Levels.diff owned !resumed) d) args
      end
      else all (f :: args)
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> all args
    | Core.Expr.Persistent_array {elements = elems; default} -> all (default :: Array.to_list elems)
    (* A closure's body is a region of its own. *)
    | Core.Expr.Lambda _ | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ ->
      List.iter
        (fun (l, o) -> captured := (o, Levels.mem l owned || Levels.mem l copied) :: !captured)
        (closure_reads d t)
    | Core.Expr.Let {binder = x; binder_type = ty; value = a; body = b; occurrence} ->
      own owned d a;
      bound d ty;
      (* What a local fixpoint closes over, it reads by reference. *)
      let owned_b =
        match a with Core.Expr.Fixpoint _
          | Core.Expr.Cofixpoint _ -> Levels.diff owned (free Parents.empty d a) | _ -> owned
      in
      let owned_b, added = after_resume owned_b d a occurrence in
      saving d a occurrence owned (fun () ->
          resuming added (fun () ->
              own (if let_owned owned d x ty a occurrence then Levels.add d owned_b else owned_b) (d + 1) b ) )
    | Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches; _} ->
      own owned d scrut;
      Array.iteri
        (fun k ({Core.Match.Branch.binders = ids; pattern = pat; body = body; _} as branch) ->
          let enclosing = !handles in
          List.iteri (fun i (_, ty) -> bound (d + i) ty) ids;
          ( match pat with
          | Core.Pattern.Constructor {constructor = r; _} when not (Base.Table.is_custom_match branches) ->
            let stored = Base.Type_util.Ctor_fields.of_ctor r in
            List.iteri
              (fun i _ -> if Base.Type_util.Ctor_fields.behind_pointer stored i then handles := Levels.add (d + i) !handles)
              ids
          | _ -> () );
          own (branch_owned owned d t ty scrut branches k branch) (d + List.length ids) body;
          handles := enclosing )
        branches
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ -> ()
  (* [f], which plans what follows a binding of [a] at [occurrence], [d]
     deep: where the machine resumes there, a binder an enclosing frame of
     the turn holds is the handler's own, for the frame saved here to take;
     where else it is read, it is read as it was bound. *)
  and saving d a occurrence owned f =
    ( match kept_across resumes d a occurrence with
    | kept when not (Levels.is_empty kept) ->
      saved_owned := (occurrence, Levels.inter kept (Levels.union owned (frame_held_now ()))) :: !saved_owned
    | _ -> () );
    let enclosing = !frame_held in
    frame_held := Levels.union enclosing (held_across resumes d a occurrence);
    f ();
    frame_held := enclosing
  (* The call [f] applied [d] deep makes into an entry: of a local fixpoint
     applied where it is written, or of the member of the fixpoint the region
     is the body of. *)
  and entering d f = Option.map fst (machine_call resumes d f)
  and owned_var owned d i _ = Levels.mem (d - i) owned
  and let_owned owned d x ty a occurrence =
    match (x, a) with
    | Core.Binder_name.Anonymous, _ -> false
    (* A closure bound to a local is a value like any other. *)
    | _, (Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ | Core.Expr.Lambda _) ->
      at_instance arms occurrence || closure_local ~n_outer ty a
    | _ ->
      (not (Base.Type_util.core_type_is_unit ty))
      && worth_moving ty
      && not (Binding.projects_in_place ~owned:(owned_var owned d) ~fate:(fate_in reads) ty a)
  and branch_owned owned d case ty scrut branches k {Core.Match.Branch.binders = ids; pattern = pat; body = body; _} =
    let n = List.length ids in
    let fields p =
      Levels.of_list (List.filteri (fun i _ -> p i (List.nth ids i)) (List.init n (fun i -> d + i)))
    in
    let reads_scrutinee body =
      match scrutinee_storage scrut with
      | Some (i, _) -> Core_plan.Escape.nb_occur_match (i + n) body > 0
      | None -> false
    in
    let ind = matched_inductive branches in
    match scrutinee_var scrut with
    | Some (i, o)
      when List.exists
             (function
               | Rebuild a -> a.branch = k && Core.Occurrence.equal a.scrutinee o
               | Fields _ | Instance _ -> false )
             arms ->
      (* Rebuilding in the scrutinee's storage moves every field out of it. *)
      Levels.union (Levels.remove (d - i) owned) (fields (fun _ _ -> true))
    | _ -> (
      match Core_plan.Match_kind.classify ty branches with
      | Custom ->
        if Binding.pair_by_value ~owned:(owned_var owned d) scrut branches then
          Levels.union owned (fields (fun _ (_, ty) -> worth_moving ty))
        else
          (* A binder the template declares as a variable of its own holds a
             copy, whoever owns the scrutinee. *)
          Levels.union owned (fields (fun j (_, ty) -> copied_binder branches k j && worth_moving ty))
      | Record _ -> (
        match List.find_map (function Fields f when f.case == case -> Some f.by_value | _ -> None) arms with
        | Some by_value ->
          Levels.union owned (fields (fun i (_, ty) -> List.nth_opt by_value i = Some true && worth_moving ty))
        | None -> owned )
      | Variant -> (
        match (pat, ind) with
        | Core.Pattern.Constructor {constructor = r; _}, Some ind
          when (not (Base.Table.is_enum_inductive ind)) && not (Base.Table.is_shared_variant ind) ->
          (* An owned variant is matched through references into it: it is
             not read whole by value while the branch runs, and its fields
             are the branch's own unless the branch reads it whole. *)
          let consumed = Binding.owns_scrutinee ~owned:(owned_var owned d) ~fate:(fate_in ~whole:true reads) scrut in
          let owned =
            match scrutinee_storage scrut with
            | Some (i, o) when owned_var owned d i o -> Levels.remove (d - i) owned
            | _ -> owned
          in
          if consumed && not (reads_scrutinee body) then
            let stored = Base.Type_util.Ctor_fields.of_ctor r in
            Levels.union owned (fields (fun i _ -> not (Base.Type_util.Ctor_fields.behind_pointer stored i)))
          else owned
        | _ -> owned ) )
  in
  own owned 0 t;
  (!out, !read_types, !captured, !copied_reads, !saved_owned, !entry_owned)

(* The plan of [root] from what {!liveness} found of it, with which reads,
   captures, saves and entries own their variable ({!ownership}). *)
let plan ~effects ~n_outer ~outer ~resumes ~certain root root_owned root_copied arms
  (reads, captures, entered, saves, entries) =
  let owned, read_types, captured_owned, copied_reads, saved_owned, entry_owned =
    ownership ~effects ~n_outer ~outer ~resumes ~certain ~reads ~arms ~owned:root_owned ~copied:root_copied root
  in
  { root;
    n_outer;
    outer;
    resumes;
    certain;
    root_owned;
    root_copied;
    arms;
    reads;
    owned;
    read_types;
    captures;
    captured_owned;
    copied_reads;
    entered;
    saves;
    saved_owned;
    entries;
    entry_owned;
    effects }

(* The reads of [t] and the saves of the machine it is lowered as: where it
   may be generated as it is, its reads planned as they are there. *)
let liveness_of ~effects ~n_outer ~copied ~arms ~resumes ~certain t =
  let lowered = liveness ~effects ~n_outer ~copied ~arms ~resumes t in
  if certain || Option.is_empty resumes then lowered
  else
    let reads, captures, entered, _, _ = liveness ~effects ~n_outer ~copied ~arms ~resumes:None t in
    let _, _, _, saves, _ = lowered in
    (reads, captures, entered, saves, [])

let region ?(owned = []) ?(copied = []) ?(outer = fun _ -> None) ?resumes ?(certain = true) ~effects ~n_outer t =
  let levels is = Levels.of_list (List.map (fun i -> -i) is) in
  plan ~effects ~n_outer ~outer ~resumes ~certain t (levels owned) (levels copied) []
    (liveness_of ~effects ~n_outer ~copied:(levels copied) ~arms:[] ~resumes ~certain t)

(* The branches of the match in [root] on the variable read at [o]. *)
let branches_at root o =
  let exception Found of Core.Match.Branch.t array in
  let rec find = function
    | Core.Expr.Match {scrutinee = scrut;
                       branches = brs; _}
                         when Option.equal Core.Occurrence.equal (Option.map snd (scrutinee_var scrut)) (Some o) ->
      raise (Found brs)
    | a -> Base.Core_util.ast_iter find a
  in
  match find root with () -> None | exception Found brs -> Some brs

(* The storage a rebuilding branch frees is taken by a construction of
   [constructor] the branch returns -- one per path, so the token is spent
   at most once -- and by nothing it merely passes to a call or a closure. *)
let reuse_arm p ~scrutinee ~branch ~constructor =
  match scrutinee_var scrutinee with
  | Some (_, scrutinee) ->
    let consumers =
      match branches_at p.root scrutinee with
      | Some brs when branch < Array.length brs ->
        let {Core.Match.Branch.body = body; _} = brs.(branch) in
        List.filter
          (function Core.Expr.Construct {constructor = r; _} -> Base.Common.globref_equal r constructor | _ -> false)
          (Core_plan.Escape.tail_constructions body)
      | _ -> []
    in
    if consumers = [] && Base.Probe.checking () then
      Base.Probe.violation "reuse plan"
        Pp.(str "a branch rebuilding in its scrutinee's storage returns no construction to take it");
    plan ~effects:p.effects ~n_outer:p.n_outer ~outer:p.outer ~resumes:p.resumes ~certain:p.certain p.root
      p.root_owned p.root_copied
      (Rebuild {scrutinee; branch; consumers} :: p.arms)
      (p.reads, p.captures, p.entered, p.saves, p.entries)
  | None -> p

module Allocation = struct
  type t = Fresh | Reuse
end

let allocation p construction : Allocation.t =
  match List.find_map (function Rebuild a -> Some a.consumers | Fields _ | Instance _ -> None) p.arms with
  | Some consumers when List.memq construction consumers -> Reuse
  | _ -> Fresh

let fields_by_value p ~case ~by_value =
  if p == empty then p
  else
    plan ~effects:p.effects ~n_outer:p.n_outer ~outer:p.outer ~resumes:p.resumes ~certain:p.certain p.root p.root_owned
      p.root_copied (Fields {case; by_value} :: p.arms)
      (p.reads, p.captures, p.entered, p.saves, p.entries)

(* Unlike the other arms, this one changes what a closure reads where it is
   made, so the reads are planned again. *)
let bound_at_instance p ~let_ =
  if p == empty then p
  else
    let arms = Instance let_ :: p.arms in
    plan ~effects:p.effects ~n_outer:p.n_outer ~outer:p.outer ~resumes:p.resumes ~certain:p.certain p.root
      p.root_owned p.root_copied arms
      (liveness_of ~effects:p.effects ~n_outer:p.n_outer ~copied:p.root_copied ~arms ~resumes:p.resumes
        ~certain:p.certain p.root)

let closure_local p ty a = if p == empty then None else Some (closure_local ~n_outer:p.n_outer ty a)

(* Whether the variable the read [o] reads is owned there: [None] of a read
   not planned, and owned only where every copy of the read is. *)
let owned_at p o =
  match List.filter (fun (o', _) -> Core.Occurrence.equal o o') p.owned with
  | [] -> None
  | copies -> Some (List.for_all snd copies)

let owned p _ o = owned_at p o = Some true

module Use = struct
  type t = Move | Share | Clone | Copy | Borrow

  let of_copy = function Retain -> Share | Duplicate -> Clone | Bits -> Copy
end

let read_type_at p o = List.find_map (fun (o', ty) -> if Core.Occurrence.equal o o' then Some ty else None) p.read_types

let read_is_typed p o =
  let rec typed = function
    | Core.Type.Meta {contents = Some t} -> typed t
    | Core.Type.Unknown | Core.Type.Meta {contents = None} | Core.Type.Hole _ -> false
    | _ -> true
  in
  match read_type_at p o with Some (Some t) -> typed t | Some None | None -> false

let use ?(whole = false) ?(boxed = false) p o : Use.t option =
  let whole = whole || boxed in
  match fate ~whole p o with
  | Last_use when owned p 0 o -> Some Move
  | Inspected when whole && owned p 0 o -> Some Move
  | Inspected -> Some Borrow
  (* A copy of a box copies the value it holds. *)
  | (Last_use | Read_again) when boxed -> Some Clone
  | Last_use | Read_again -> (
    match Option.map copy_of_type (Option.flatten (read_type_at p o)) with
    | Some (Some c) -> Some (Use.of_copy c)
    | Some None | None ->
      (* Inference left the type unsolved where the read is lowered: no
         reading of the C++ declaration stands in for it. *)
      Base.Probe.violation "copy mode" (Pp.str "a read whose Core type inference left unsolved is copied");
      Some Clone )
  | Unplanned -> None

(* Whether [p] moves the read [o]: {!use}'s [Move], asked where what a copy
   would be is not the question. *)
let moves ?(whole = false) p o =
  match fate ~whole p o with
  | Last_use -> owned p 0 o
  | Inspected -> whole && owned p 0 o
  | Read_again | Unplanned -> false

let copy_of_declared ty = Use.of_copy (copy_of_cpp ty)

(* The arguments the local fixpoint applied at [at] reads before the call:
   each reading a variable, or a part of one, that a later one moves -- by
   a read the plan moves, or a capture it takes by move.  The call alone
   leaves its arguments unordered. *)
let evaluated_first p at =
  match List.find_opt (fun e -> Core.Occurrence.equal e.at at) p.entered with
  | None -> []
  | Some e ->
    let moved (_, o) = moves p o || fate_in p.captures o = Last_use in
    let moves = List.map (fun a -> List.filter moved a.read_at) e.arguments in
    List.filter_map
      (fun (j, a) ->
        let later = List.concat (List.filteri (fun k _ -> k > j) moves) in
        if List.exists (fun (l, _) -> Levels.exists (fun m -> e.overlaps m l) a.variables) later then Some j else None )
      (List.mapi (fun j a -> (j, a)) e.arguments)

(* A turn of a loop as the Core it runs, standing under the loop's
   parameters, where it is one a region plans: lets and matches as they
   are, a [Continue] the application of nothing to its arguments -- what
   follows a turn is the next one, which the parameter a turn passes a new
   value no longer reads -- and the cells a [Continue_into] builds made
   beside its arguments, in no order.  A machine's [Resume]s and entries
   run turns of their own: none is planned. *)
exception Unplanned_turn

let turn_term ?(arguments = fun (c : Control_ir.Term.continue_) -> c.arguments) t =
  let rec go : Control_ir.Term.t -> Core.Expr.t = function
    | Loop inner -> go inner.body
    | Let {binder; binder_type; value; body} ->
      Core.Expr.Let {binder; binder_type; value; body = go body; occurrence = Core.Occurrence.fresh ()}
    | Match {scrutinee_type; scrutinee; branches} ->
      Core.Expr.Match {scrutinee_type; scrutinee; branches = Array.of_list
            (List.map
               (fun (b : Control_ir.Term.branch) ->
                 { Core.Match.Branch.binders = b.binders;
                   result_type = b.result_type;
                   pattern = b.pattern;
                   body = go b.body })
               branches); occurrence = Core.Occurrence.fresh ()}
    | Return t -> t
    | Continue c -> Core.Expr.Apply {callee = Core.Expr.Erased_value Core.Erasure_reason.Proof; arguments = arguments c}
    | Continue_into {cells; next} ->
      Core.Expr.Tuple
        (List.concat_map (fun (c : Control_ir.Term.cell) -> c.arguments) cells
          @ [Core.Expr.Apply {callee = Core.Expr.Erased_value Core.Erasure_reason.Proof; arguments = arguments next}])
    | Resume _ | Entry _ -> raise Unplanned_turn
  in
  go t

module Continue_move = struct
  type t = Keep | Move_parameter | Move_argument
end

let continue_moves ~effects (l : Control_ir.Term.loop) =
  match turn_term l.body with
  | exception Unplanned_turn -> []
  | body ->
    let p = region ~effects ~n_outer:0 body in
    let n = List.length l.parameters in
    (* The reads in [t], standing where the Continue does, of what the index
       [db] names there. *)
    let reads_of db t = List.filter_map (fun (l, o) -> if l = -db then Some o else None) (closure_reads 0 t) in
    (* Whether the read [o] of the local [k] the argument at [i] of the
       Continue [c] is would be a move were [c]'s other arguments not to
       name [k]: the turn planned again with those reads erased.  A read of
       a part of [k] there is left, and keeps [o] from being the last. *)
    let last_but_by_name (c : Control_ir.Term.continue_) i k o =
      moves ~whole:true p o
      ||
      let rec erase n t =
        match t with Core.Expr.Bound_variable {index = j; _}
          when j = n -> Core.Expr.Erased_value Core.Erasure_reason.Proof | t -> Base.Core_util.ast_map_lift erase n t in
      let arguments (c' : Control_ir.Term.continue_) =
        if Core.Occurrence.equal c'.occurrence c.occurrence then
          List.mapi (fun j a -> if j = i then a else erase k a) c'.arguments
        else c'.arguments
      in
      match turn_term ~arguments l.body with
      | exception Unplanned_turn -> false
      | body -> moves ~whole:true (region ~effects ~n_outer:0 body) o
    in
    let moves depth (c : Control_ir.Term.continue_) =
      List.mapi
        (fun i ((_, ty), argument) : Continue_move.t ->
          match (reads_of (n - i + depth) argument, strip argument) with
          | [o], argument
            when worth_moving ty
                 && (match argument with Core.Expr.Bound_variable _ -> false | _ -> true)
                 && fate ~whole:true p o = Last_use ->
            Move_parameter
          (* A local of the turn -- [depth] binders stand between the
             Continue and the loop's parameters -- owned, read whole, and
             read after by nothing but this Continue's other arguments,
             naming it. *)
          | [], Core.Expr.Bound_variable {index = k; occurrence = o} when k <= depth && worth_moving ty
            && last_but_by_name c i k o ->
            Move_argument
          | _ -> Keep )
        (List.combine l.parameters c.arguments)
    in
    let rec turns depth acc : Control_ir.Term.t -> _ = function
      | Loop inner -> turns depth acc inner.body
      | Let b -> turns (depth + 1) acc b.body
      | Match m ->
        List.fold_left
          (fun acc (b : Control_ir.Term.branch) -> turns (depth + List.length b.binders) acc b.body) acc m.branches
      | Return _ | Resume _ | Entry _ -> acc
      | Continue c | Continue_into {next = c; _} ->
        if Control_ir.Loop.equal c.target l.loop && List.compare_lengths c.arguments l.parameters = 0 then
          (c.occurrence, moves depth c) :: acc
        else acc
    in
    List.rev (turns 0 [] l.body)

let rec takes_record ~throws p t =
  match t with
  | Core.Expr.Bound_variable {occurrence = o; _} -> moves p o
  | Core.Expr.Global {callee = r; _} -> Base.Table.is_cofixpoint r || throws r
  | t -> ( match field_of t with Some r -> takes_record ~throws p r | None -> true )

let owns_scrutinee p = Binding.owns_scrutinee ~owned:(owned p) ~fate:(fate ~whole:true p)

let pair_by_value p = Binding.pair_by_value ~owned:(owned p)

let projects_in_place p = Binding.projects_in_place ~owned:(owned p) ~fate:(fate p)

(* Whether a closure made around the read [o] -- one Core does not contain,
   or an eta closure around an argument -- takes its variable by move: the
   read takes the whole value, and the variable, or the copy closures take
   of it, is owned. *)
let taken_by_closure p o =
  ( match fate ~whole:true p o with Last_use | Inspected -> true | Read_again | Unplanned -> false )
  && (owned p 0 o || List.exists (Core.Occurrence.equal o) p.copied_reads)

(* The variables, by de Bruijn index at [closure], that [closure] takes by
   move: every read of each inside it is a last use, of a variable owned
   where the closure is made. *)
let moved_captures p closure =
  let every l o = match List.filter (fun (o', _) -> Core.Occurrence.equal o o') l with
    | [] -> false
    | copies -> List.for_all snd copies
  in
  (* A read the region makes outside any closure, inside one translation
     made around it -- a partial application eta-expanded -- is taken where
     that closure is made, which is where the read stood. *)
  let moves o =
    match fate_in p.captures o with
    | Unplanned -> taken_by_closure p o
    | fate -> fate = Last_use && every p.captured_owned o
  in
  let reads = closure_reads 0 closure in
  List.sort_uniq Int.compare
    (List.filter_map
       (fun (l, _) ->
         if List.for_all (fun (l', o) -> l' <> l || moves o) reads then Some (-l) else None )
       reads )

(* {!moved_captures} of the fixpoint [fix], given to the last of its
   functions reading each variable, by index at [fix]. *)
let moved_captures_by_member p fix =
  match fix with
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let funs = Core.Recursion.Group.bodies rec_group in
    let n = Array.length funs in
    let reads =
      Array.map
        (fun f -> List.filter_map (fun (l, _) -> if -l - n > 0 then Some (-l - n) else None) (closure_reads 0 f))
        funs
    in
    let last_reader d =
      Array.fold_left (fun (j, last) r -> (j + 1, if List.mem d r then Some j else last)) (0, None) reads |> snd
    in
    let taken = Array.make n [] in
    List.iter
      (fun d -> Option.iter (fun j -> taken.(j) <- d :: taken.(j)) (last_reader d))
      (moved_captures p fix);
    Array.to_list (Array.map (List.sort_uniq Int.compare) taken)
  | _ -> []

(* The variables, by index where [ts] stand, that a closure made around
   [ts] takes by move ({!eta_captures}). *)
let moved_reads p ts =
  let rec go acc = function
    | Core.Expr.Bound_variable {index = i; occurrence = o} -> if taken_by_closure p o then i :: acc else acc
    | Core.Expr.Coerce {value = t; _}
    | Core.Expr.Boxed_value {value = t; _}
    | Core.Expr.Lambda_group_barrier {value = t; _} -> go acc t
    | Core.Expr.Apply {callee = f; arguments = args} -> List.fold_left go acc (f :: args)
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.fold_left go acc args
    (* What a closure among them takes by move, the closure made around
       them takes by move first, to hand it on. *)
    | (Core.Expr.Lambda _ | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _) as closure -> moved_captures p closure @ acc
    | _ -> acc
  in
  List.sort_uniq Int.compare (List.fold_left go [] ts)

module Capture = struct
  type t = By_reference | By_move | Shared
end

module Storage = struct
  type t = Local | Frame
end

(* The variables [ts] read, at the index each has where they stand, in
   order, once each. *)
let read_indices ts =
  List.sort_uniq Int.compare (List.concat_map (fun t -> List.map (fun (l, _) -> -l) (closure_reads 0 t)) ts)

let mode_of moved i : Capture.t = if List.mem i moved then By_move else Shared

let captures ?(in_place = false) p closure =
  let moved = if in_place then [] else moved_captures p closure in
  List.map (fun i -> (i, if in_place then Capture.By_reference else mode_of moved i)) (read_indices [closure])

let captures_by_member ?(in_place = false) p fix =
  match fix with
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let funs = Core.Recursion.Group.bodies rec_group in
    let n = Array.length funs in
    let moved = if in_place then List.map (fun _ -> []) (Array.to_list funs) else moved_captures_by_member p fix in
    List.map2
      (fun f moved ->
        let read =
          List.sort_uniq Int.compare
            (List.filter_map (fun (l, _) -> if -l - n > 0 then Some (-l - n) else None) (closure_reads 0 f)) in
        List.map (fun i -> (i, if in_place then Capture.By_reference else mode_of moved i)) read )
      (Array.to_list funs) moved
  | _ -> []

let eta_captures p ts =
  let moved = moved_reads p ts in
  List.map (fun i -> (i, mode_of moved i)) (read_indices ts)

module Local_passing = struct
  type t = Cpp_ir.Param_mode.ownership option list

  let recorded : ((Core.Occurrence.t * int) * t) list ref = Base.State.cell Base.State.Extraction []

  let same (o, j) (o', j') = Core.Occurrence.equal o o' && Int.equal j j'

  let lookup member = List.find_map (fun (m, t) -> if same m member then Some t else None) !recorded

  let record member t =
    match lookup member with
    | Some t' when t' = t -> ()
    | Some _ ->
      Base.Probe.violation "local passing"
        (Pp.str "a local fixpoint is generated passing its parameters otherwise than it was before");
      recorded := (member, t) :: List.filter (fun (m, _) -> not (same m member)) !recorded
    | None -> recorded := (member, t) :: !recorded
end

let kept_by_frame p b =
  List.exists
    (fun s -> List.exists (fun (b', _, _) -> Core.Binder.equal b b' && Core.Binder.same_site b b') s.saved)
    p.saves

module Local_captures = struct
  let recorded : ((Core.Occurrence.t * int) * Capture.t list) list ref = Base.State.cell Base.State.Extraction []

  let lookup member = List.find_map (fun (m, t) -> if Local_passing.same m member then Some t else None) !recorded

  let record member modes =
    recorded := (member, modes) :: List.filter (fun (m, _) -> not (Local_passing.same m member)) !recorded

  let by_reference member = match lookup member with Some modes -> List.mem Capture.By_reference modes | None -> false
end

let save_moves p let_ =
  match List.filter (fun s -> Core.Occurrence.equal s.save_at let_) p.saves with
  | [] -> None
  | saves ->
    let owned =
      match List.filter_map (fun (o, l) -> if Core.Occurrence.equal o let_ then Some l else None) p.saved_owned with
      | [] -> Levels.empty
      | l :: ls -> List.fold_left Levels.inter l ls
    in
    let moved (b, l, _) =
      Levels.mem l owned
      && List.for_all
           (fun s -> List.exists (fun (b', l', last) -> l' = l && Core.Binder.equal b b' && last) s.saved)
           saves
    in
    Some (List.filter_map (fun ((b, _, _) as s) -> if moved s then Some b else None) (List.hd saves).saved)

module Frame_save = struct
  type t = Core.Binder.t list

  let recorded : (Core.Binder.t * t) list ref = Base.State.cell Base.State.Extraction []

  let same b b' = Core.Binder.equal b b' && Core.Binder.same_site b b'

  let lookup binder = List.find_map (fun (b, t) -> if same b binder then Some t else None) !recorded

  let alternatives = Base.State.cell Base.State.Extraction 0

  let generating_alternatives f =
    alternatives := !alternatives + 1;
    Fun.protect ~finally:(fun () -> alternatives := !alternatives - 1) f

  let record binder t =
    match lookup binder with
    | Some t' when List.equal Core.Binder.equal t t' -> ()
    | Some t' ->
      if !alternatives = 0 then
        Base.Probe.violation "frame save"
          (Pp.str "a let a frame machine resumes at is generated saving its frame otherwise than it was before");
      let both = List.filter (fun b -> List.exists (Core.Binder.equal b) t') t in
      recorded := (binder, both) :: List.filter (fun (b, _) -> not (same b binder)) !recorded
    | None -> recorded := (binder, t) :: !recorded
end

let entry_moves p =
  match p.resumes with
  | Some {origin; depth; _} when p.certain ->
    let calls =
      List.fold_left
        (fun acc e -> if List.exists (Core.Occurrence.equal e.call) acc then acc else e.call :: acc)
        [] p.entries
    in
    List.map
      (fun call ->
        let here = List.filter (fun e -> Core.Occurrence.equal e.call call) p.entries in
        let owned =
          match List.filter_map (fun (o, l) -> if Core.Occurrence.equal o call then Some l else None) p.entry_owned with
          | [] -> Levels.empty
          | l :: ls -> List.fold_left Levels.inter l ls
        in
        let moved e =
          List.filter_map (fun (l, last) -> if last && Levels.mem l owned then Some l else None) e.captured
          @ List.filter_map
              (fun (l, o) ->
                if fate_in p.reads o = Last_use && (owned_at p o = Some true || Levels.mem l owned)
                  then Some l else None )
              e.arguments
        in
        let levels =
          match List.map (fun e -> Levels.of_list (moved e)) here with
          | [] -> Levels.empty
          | l :: ls -> List.fold_left Levels.inter l ls
        in
        (call, List.map (fun l -> Core.Binder.make ~origin ~level:(depth + l) ()) (Levels.elements levels)) )
      calls
  | Some _ | None -> []

type region_plan = t

module Entry_moves = struct
  type t = Core.Binder.t list

  let recorded : (Core.Occurrence.t * t) list ref = Base.State.cell Base.State.Extraction []

  let lookup call = List.find_map (fun (c, t) -> if Core.Occurrence.equal c call then Some t else None) !recorded

  let record call t =
    match lookup call with
    | Some t' when List.equal Core.Binder.equal t t' -> ()
    | Some t' ->
      Base.Probe.violation "entry moves"
        (Pp.str "a call entering an adopted entry is planned moving otherwise than it was before");
      let both = List.filter (fun b -> List.exists (Core.Binder.equal b) t') t in
      recorded := (call, both) :: List.filter (fun (c, _) -> not (Core.Occurrence.equal c call)) !recorded
    | None -> recorded := (call, t) :: !recorded

  let record_plan p = List.iter (fun (call, t) -> record call t) (entry_moves p)
end
