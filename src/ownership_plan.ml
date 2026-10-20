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

type t = read list

let empty = []

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

let region t =
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

let fate p o =
  match List.filter (fun r -> Occurrence.equal o r.occurrence) p with
  | [] -> Unplanned
  | copies ->
    if not (List.for_all (fun r -> r.last) copies) then Read_again
    else if List.for_all (fun r -> r.consumed) copies then Last_use
    else Inspected
