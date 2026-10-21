(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which reads of a local are its last use.  See [ownership_plan.mli]. *)

open Miniml

module Levels = Set.Make (Int)
module Parents = Map.Make (Int)

(* Every read the region holds, in no order. *)
type read = {
  occurrence : Occurrence.t;
  last : bool;  (* nothing after it or beside it reads the variable *)
  consumed : bool;  (* where it stands, its value may be taken *)
}

(* A branch generated to rebuild in its scrutinee's storage, named by the
   scrutinee's read and the branch's index. *)
type arm = {scrutinee : Occurrence.t; branch : int}

type t = {
  root : ml_ast;
  root_owned : Levels.t;
  arms : arm list;
  reads : read list;
  owned : (Occurrence.t * bool) list;  (* whether the variable a read reads is owned there *)
}

let empty =
  {root = MLdummy Kprop; root_owned = Levels.empty; arms = []; reads = []; owned = []}

let worth_moving ty = Escape.is_shared_ptr_type ty || Ml_type_util.is_nontrivial_value_ml_type ty

(* A variable is named by its de Bruijn level in the region: the number of
   binders around its binding site, counted from the region's root, so that
   one the region does not bind has a negative level.  [parents] maps a
   pattern variable to the variable its match took apart. *)

let rec ancestors parents l =
  match Parents.find_opt l parents with Some p -> p :: ancestors parents p | None -> []

(* Two variables share storage when one is the other, or a part of it. *)
let overlap parents l m = l = m || List.mem m (ancestors parents l) || List.mem l (ancestors parents m)

(* The variables of [s] seen from [d] binders deep, leaving the scope of the
   binders at [d] and deeper: a part stays a read of the nearest variable it
   is a part of that is still in scope, anything else is dropped. *)
let leave parents d s =
  Levels.filter_map
    (fun l ->
      if l < d then Some l else List.find_opt (fun p -> p < d) (ancestors parents l) )
    s

let rec strip = function MLmagic (_, t) -> strip t | t -> t

(* What a match's pattern variables are parts of: the variable it matches,
   when it matches one. *)
let bind_parts parents d ~n scrut =
  let rec go parents l =
    if l >= d + n then parents
    else
      let parents =
        match strip scrut with
        | MLrel (i, _) -> Parents.add l (d - i) parents
        | _ -> Parents.remove l parents
      in
      go parents (l + 1)
  in
  go parents d

let bind parents d ~n =
  let rec go parents l = if l >= d + n then parents else go (Parents.remove l parents) (l + 1) in
  go parents d

(* The variables bound outside [t] that [t] reads, [t] standing [d] binders
   deep. *)
let rec free parents d t =
  match t with
  | MLrel (i, _) -> if i > 0 then Levels.singleton (d - i) else Levels.empty
  | MLmagic (_, t) -> free parents d t
  | MLapp (f, args) -> frees parents d (f :: args)
  | MLcons (_, _, args) | MLtuple args -> frees parents d args
  | MLparray (elems, default) -> frees parents d (default :: Array.to_list elems)
  | MLlam (_, _, body) -> under parents d ~n:1 body
  | MLletin (_, _, a, b, _) -> Levels.union (free parents d a) (under parents d ~n:1 b)
  | MLfix (_, fs, defs, _, _) ->
    let n = Array.length fs in
    let parents' = bind parents d ~n in
    leave parents' d (frees parents' (d + n) (Array.to_list defs))
  | MLcase (_, scrut, branches) ->
    Array.fold_left
      (fun acc (ids, _, _, body) ->
        let n = List.length ids in
        let parents' = bind_parts parents d ~n scrut in
        Levels.union acc (leave parents' d (free parents' (d + n) body)) )
      (free parents d scrut) branches
  | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> Levels.empty

and frees parents d ts = List.fold_left (fun acc t -> Levels.union acc (free parents d t)) Levels.empty ts

and under parents d ~n body =
  let parents' = bind parents d ~n in
  leave parents' d (free parents' (d + n) body)

(* Whether the closure a let binds may read what it closes over at its uses
   rather than where it is made: a local fixpoint closes over its
   surroundings by reference, and a lambda polymorphic in a type variable may
   be lifted to a function template, to which each use passes them, or
   inlined at each use.  A monomorphic lambda is a value holding copies. *)
let reads_at_uses ty a =
  match strip a with
  | MLfix _ -> true
  | MLlam _ -> not (Mlutil.IntSet.is_empty (Mlutil.ml_tvars ty))
  | _ -> false

(* Whether a match may take its scrutinee's value, as translation generates
   it.  A variant's alternatives are bound by reference into the scrutinee,
   which a variable that is matched keeps; a custom match whose template
   spells the scrutinee twice would move it twice.  An enum is a value, a
   record's fields are read one at a time, and any other custom match
   evaluates its scrutinee once. *)
let scrutinee_consumed ty scrut branches =
  if Table.is_custom_match branches then
    let uses =
      List.length
        (List.filter (( = ) Foreign_template.CCscrut)
           (Foreign_template.match_template (Table.find_custom_match branches)) )
    in
    uses <= 1 || (match strip scrut with MLrel _ -> false | _ -> true)
  else if Table.record_fields_of_type ty <> [] && Array.length branches = 1 then true
  else
    Array.for_all
      (fun (_, _, pat, _) ->
        match pat with
        | Pusual (Names.GlobRef.ConstructRef (ip, _)) | Pcons (Names.GlobRef.ConstructRef (ip, _), _) ->
          Table.is_enum_inductive (Names.GlobRef.IndRef ip)
        | _ -> true )
      branches

(* How many times an argument of [r] is evaluated: an inline custom splices
   it as often as its template names it. *)
let evaluations r =
  match Table.inline_custom_text r with
  | Some s when Table.is_inline_custom r -> Foreign_template.arg_mentions s
  | _ -> fun _ -> 1

let liveness t =
  let reads = ref [] in
  (* [walk ~consumed ~pinned parents d live t] records [t]'s reads and is
     what is live before [t], given [live] after it: both sets of variables
     in scope at [t], [d] binders deep.  [consumed] is whether [t] stands
     where its value may be taken. *)
  let rec walk ?(consumed = true) ~pinned parents d live t =
    let walk ?(consumed = consumed) = walk ~consumed in
    let unsequenced ?(consumed = consumed) ?evaluated = unsequenced ~consumed ?evaluated in
    match t with
    | MLrel (i, occurrence) ->
      let l = d - i in
      let shared = Levels.exists (overlap parents l) in
      reads := {occurrence; last = not (shared live || shared pinned); consumed} :: !reads;
      Levels.add l live
    | MLmagic (_, t) -> walk ~pinned parents d live t
    | MLapp (MLglob {callee = r; _}, args) when Table.is_inline_custom r ->
      unsequenced ~evaluated:(evaluations r) ~pinned parents d live args
    (* A bind generated as sequencing runs its action and then its
       continuation's body, inline. *)
    | MLapp (MLglob use, (_ :: _ :: _ as args))
      when Core_effects.find use = Some {operation = Bind; mode = Sequential} -> (
      let action, k = Common.last_two args in
      match Mlutil.collect_lams k with
      | [], _ -> walk ~pinned parents d (walk ~pinned parents d live k) action
      | ids, body ->
        let n = List.length ids in
        let parents' = bind parents d ~n in
        let live_body = walk ~pinned parents' (d + n) live body in
        walk ~pinned parents d (leave parents' d live_body) action )
    | MLapp (f, args) -> unsequenced ~pinned parents d live (f :: args)
    (* A record's fields are copied into it. *)
    | MLcons (ty, _, args) when Table.record_fields_of_type ty <> [] ->
      unsequenced ~consumed:false ~pinned parents d live args
    | MLcons (_, _, args) | MLtuple args -> unsequenced ~pinned parents d live args
    | MLparray (elems, default) ->
      unsequenced ~pinned parents d live (default :: Array.to_list elems)
    (* A closure reads what it closes over where it is made; its own body
       is a region of its own. *)
    | MLlam _ | MLfix _ -> Levels.union live (free parents d t)
    | MLletin (_, ty, a, b, _) ->
      let pinned_b = if reads_at_uses ty a then Levels.union pinned (free parents d a) else pinned in
      let parents_b = bind parents d ~n:1 in
      let live_b = walk ~pinned:pinned_b parents_b (d + 1) live b in
      walk ~pinned parents d (leave parents_b d live_b) a
    (* A branch reads its pattern variables through the scrutinee's own
       evaluation -- a field of the record it names, a component of the pair
       it hands over -- so what follows the scrutinee is what the branches
       read besides them. *)
    | MLcase (ty, scrut, branches) ->
      let after_scrut =
        Array.fold_left
          (fun acc (ids, _, _, body) ->
            let n = List.length ids in
            let live_body = walk ~pinned (bind_parts parents d ~n scrut) (d + n) live body in
            Levels.union acc (leave (bind parents d ~n) d live_body) )
          Levels.empty branches
      in
      walk
        ~consumed:(consumed && scrutinee_consumed ty scrut branches)
        ~pinned parents d after_scrut scrut
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> live
  (* The terms of [ts] are evaluated in no fixed order: each is followed by
     whatever the others read, and by what it reads itself when it is
     evaluated twice.  One evaluated not at all reads nothing. *)
  and unsequenced ~consumed ?(evaluated = fun _ -> 1) ~pinned parents d live ts =
    let reads_of = List.map (free parents d) ts in
    List.mapi
      (fun k t ->
        match evaluated k with
        | 0 -> live
        | m ->
          let others = List.filteri (fun j _ -> j <> k || m > 1) reads_of in
          walk ~consumed ~pinned parents d (List.fold_left Levels.union live others) t )
      ts
    |> List.fold_left Levels.union live
  in
  ignore (walk ~pinned:Levels.empty Parents.empty 0 Levels.empty t);
  !reads

type fate = Last_use | Read_again | Inspected | Unplanned

let fate_in reads o =
  match List.filter (fun r -> Occurrence.equal o r.occurrence) reads with
  | [] -> Unplanned
  | copies ->
    if not (List.for_all (fun r -> r.last) copies) then Read_again
    else if List.for_all (fun r -> r.consumed) copies then Last_use
    else Inspected

let fate p o = fate_in p.reads o

let sequential_bind use = Core_effects.find use = Some {operation = Bind; mode = Sequential}

(* The inductive a match's branches take apart, if one names a constructor. *)
let matched_inductive branches =
  Array.fold_left
    (fun acc (_, _, pat, _) ->
      match (acc, pat) with
      | None, (Pusual (Names.GlobRef.ConstructRef (ip, _)) | Pcons (Names.GlobRef.ConstructRef (ip, _), _))
        ->
        Some (Names.GlobRef.IndRef ip)
      | _ -> acc )
    None branches

(* The variable whose storage a match reads its fields out of: through a
   magic cast, and through the application that instantiates a binder of
   dependent type at its witness.  Only a scrutinee that is the variable
   itself is taken apart as a value the region owns; one named through an
   application is read in place. *)
let rec scrutinee_storage = function
  | MLrel (i, o) -> Some (i, o)
  | MLmagic (_, t) | MLapp (t, _) -> scrutinee_storage t
  | _ -> None

let scrutinee_var scrut = match strip scrut with MLrel (i, o) -> Some (i, o) | _ -> None

(* The binding modes a region's lowering gives its binders, as functions of
   whether a read's variable is owned where it is read ([owned]) and of the
   read's fate ([fate]). *)
module Binding = struct
  (* A custom match takes a pair apart by value when it is the pair's last
     reader: a pair the scrutinee has just built, or a variable owned there
     that the branch does not read whole. *)
  let pair_by_value ~owned scrut branches =
    Array.length branches = 1
    && (match matched_inductive branches with
       | Some r -> Ml_type_util.is_prod_global r
       | None -> false )
    &&
    match scrutinee_var scrut with
    | Some (i, o) ->
      let ids, _, _, body = branches.(0) in
      owned i o && Escape.nb_occur_match (i + List.length ids) body = 0
    | None -> true

  (* A let binds by reference the field it projects out of a record that is
     not moved there. *)
  let projects_in_place ~owned ~fate ty a =
    Escape.is_shared_ptr_type ty
    &&
    match a with
    | MLcase (_, MLrel (k, o), [|(_, _, _, MLrel _)|]) -> not (owned k o && fate o = Last_use)
    | _ -> false

  (* A variant match takes apart a scrutinee the region owns, binding its
     fields by mutable reference. *)
  let owns_scrutinee ~owned scrut =
    match scrutinee_var scrut with Some (i, o) -> owned i o | None -> false
end

(* [ownership ~reads ~arms ~owned t] says, of every read in [t], whether the
   variable it reads is owned where it is read: bound by value, so that the
   region may take its value.  [owned] holds the levels of the variables the
   region owns at its root. *)
let ownership ~reads ~arms ~owned t =
  let out = ref [] in
  let rec own owned d t =
    let all = List.iter (own owned d) in
    match t with
    | MLrel (i, occurrence) -> out := (occurrence, Levels.mem (d - i) owned) :: !out
    | MLmagic (_, t) -> own owned d t
    (* A bind generated as sequencing binds its continuation's parameter to
       the action's value. *)
    | MLapp (MLglob use, (_ :: _ :: _ as args)) when sequential_bind use -> (
      let action, k = Common.last_two args in
      own owned d action;
      match Mlutil.collect_lams k with
      | [], _ -> own owned d k
      | ((_, ty) :: _ as ids), body ->
        let n = List.length ids in
        own (if worth_moving ty then Levels.add (d + n - 1) owned else owned) (d + n) body )
    | MLapp (f, args) -> all (f :: args)
    | MLcons (_, _, args) | MLtuple args -> all args
    | MLparray (elems, default) -> all (default :: Array.to_list elems)
    (* A closure's body is a region of its own. *)
    | MLlam _ | MLfix _ -> ()
    | MLletin (x, ty, a, b, _) ->
      own owned d a;
      (* What a local fixpoint closes over, it reads by reference. *)
      let owned_b =
        match a with MLfix _ -> Levels.diff owned (free Parents.empty d a) | _ -> owned
      in
      own (if let_owned owned d x ty a then Levels.add d owned_b else owned_b) (d + 1) b
    | MLcase (ty, scrut, branches) ->
      own owned d scrut;
      Array.iteri
        (fun k ((ids, _, _, body) as branch) ->
          own (branch_owned owned d ty scrut branches k branch) (d + List.length ids) body )
        branches
    | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> ()
  and owned_var owned d i _ = Levels.mem (d - i) owned
  and let_owned owned d x ty a =
    match (x, a) with
    | Dummy, _ | _, (MLfix _ | MLlam _) -> false
    | _ ->
      (not (Ml_type_util.ml_type_is_unit ty))
      && worth_moving ty
      && not (Binding.projects_in_place ~owned:(owned_var owned d) ~fate:(fate_in reads) ty a)
  and branch_owned owned d ty scrut branches k (ids, _, pat, body) =
    let n = List.length ids in
    let fields p =
      Levels.of_list (List.filteri (fun i _ -> p i (List.nth ids i)) (List.init n (fun i -> d + i)))
    in
    let reads_scrutinee body =
      match scrutinee_storage scrut with
      | Some (i, _) -> Escape.nb_occur_match (i + n) body > 0
      | None -> false
    in
    let ind = matched_inductive branches in
    match scrutinee_var scrut with
    | Some (i, o) when List.exists (fun a -> a.branch = k && Occurrence.equal a.scrutinee o) arms ->
      (* Rebuilding in the scrutinee's storage moves every field out of it. *)
      Levels.union (Levels.remove (d - i) owned) (fields (fun _ _ -> true))
    | _ ->
      if Table.is_custom_match branches then
        if Binding.pair_by_value ~owned:(owned_var owned d) scrut branches then
          Levels.union owned (fields (fun _ (_, ty) -> worth_moving ty))
        else owned
      else if Table.record_fields_of_type ty <> [] && Array.length branches = 1 then owned
      else
        match (pat, ind) with
        | (Pusual r | Pcons (r, _)), Some ind
          when (not (Table.is_enum_inductive ind)) && not (Table.is_shared_variant ind) ->
          (* An owned variant is matched through references into it: it is
             not read whole by value while the branch runs, and its fields
             are the branch's own unless the branch reads it whole. *)
          let consumed = Binding.owns_scrutinee ~owned:(owned_var owned d) scrut in
          let owned =
            match scrutinee_storage scrut with
            | Some (i, o) when owned_var owned d i o -> Levels.remove (d - i) owned
            | _ -> owned
          in
          if consumed && not (reads_scrutinee body) then
            let stored = Ml_type_util.Ctor_fields.of_ctor r in
            Levels.union owned (fields (fun i _ -> not (Ml_type_util.Ctor_fields.behind_pointer stored i)))
          else owned
        | _ -> owned
  in
  own owned 0 t;
  !out

let plan root root_owned arms reads =
  {root; root_owned; arms; reads; owned = ownership ~reads ~arms ~owned:root_owned root}

let region ?(owned = []) t = plan t (Levels.of_list (List.map (fun i -> -i) owned)) [] (liveness t)

let reuse_arm p ~scrutinee ~branch =
  match scrutinee_var scrutinee with
  | Some (_, scrutinee) -> plan p.root p.root_owned ({scrutinee; branch} :: p.arms) p.reads
  | None -> p

let owned_at p o =
  match List.filter (fun (o', _) -> Occurrence.equal o o') p.owned with
  | [] -> None
  | copies -> Some (List.for_all snd copies)

let owned p _ o = owned_at p o = Some true

let moves p o = owned p 0 o && fate p o = Last_use

let owns_scrutinee p = Binding.owns_scrutinee ~owned:(owned p)

let pair_by_value p = Binding.pair_by_value ~owned:(owned p)

let projects_in_place p = Binding.projects_in_place ~owned:(owned p) ~fate:(fate p)
