(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

type kind =
  | No_recursion
  | Tail
  | Nontail

type group = {
  members : Names.GlobRef.t list;
  kind : kind;
}

type t = {
  groups : group list;
  by_member : group Ref.User.Map.t;
  defined : Ref.User.Set.t;
}

let empty = {groups = []; by_member = Ref.User.Map.empty; defined = Ref.User.Set.empty}

let rec split_params n = function
  | MLlam (_, _, b) -> split_params (n + 1) b
  | b -> (n, b)

(* How [fd_body], a function generated in [mode], calls the functions
   [arity_of] gives the number of parameters of -- [None] for any other
   global -- as the C++ it becomes does: a call is a tail call where its
   result is the function's, and a call the C++ wraps in a closure, or one
   applied to more arguments than its parameters, is not. *)
let classify ~arity_of ~mode fd_body =
  let _, body = split_params 0 fd_body in
  let tail_call = ref false and nontail_call = ref false in
  let effect use =
    match Core_effects.operation_of use.callee with
    | Some operation when mode = Core_effects.Sequential -> Some operation
    | _ -> None
  in
  (* A custom whose replacement text is its one argument writes nothing
     around it, so the argument is where the custom is: sequential [itree]
     maps [go] and [TauF] so, and [Tau t] is [t]. *)
  let identity r =
    Table.is_custom r
    && Minicpp.inline_shape_of_text (Table.find_custom r) = Minicpp.Inline_identity
  in
  let rec walk ~tail e =
    match e with
    | MLglob use when arity_of use.callee = Some 0 ->
      if tail then tail_call := true else nontail_call := true
    | MLcons (_, c, [a]) when identity c -> walk ~tail a
    | MLapp (MLglob use, [a]) when identity use.callee && Table.to_inline use.callee -> walk ~tail a
    | MLapp (MLglob use, args) when Option.has_some (arity_of use.callee) ->
      List.iter (walk ~tail:false) args;
      if tail && Some (List.length args) = arity_of use.callee then tail_call := true
      else nontail_call := true
    | MLapp (MLglob use, args) when effect use = Some Core_effects.Bind -> (
      (* The action runs, and the continuation's body goes on where the bind
         stands. *)
      match List.rev args with
      | k :: action :: rest ->
        List.iter (walk ~tail:false) rest;
        walk ~tail:false action;
        continuation ~tail k
      | _ -> List.iter (walk ~tail:false) args )
    | MLapp (MLglob use, args) when effect use = Some Core_effects.Return -> (
      match List.rev args with
      | value :: rest ->
        List.iter (walk ~tail:false) rest;
        walk ~tail value
      | [] -> () )
    | MLapp ((MLlam _ as f), args) ->
      List.iter (walk ~tail:false) args;
      let rec enter n = function
        | MLlam (_, _, b) when n > 0 -> enter (n - 1) b
        | b -> if n = 0 then walk ~tail b else walk ~tail:false b
      in
      enter (List.length args) f
    | MLapp (f, args) ->
      walk ~tail:false f;
      List.iter (walk ~tail:false) args
    | MLletin (_, _, a, b) ->
      walk ~tail:false a;
      walk ~tail b
    | MLcase (_, s, branches) ->
      walk ~tail:false s;
      Array.iter (fun (_, _, _, b) -> walk ~tail b) branches
    | MLmagic (_, a) -> walk ~tail a
    | MLlam (_, _, b) -> walk ~tail:false b
    | MLfix (_, _, bodies, _) -> Array.iter (walk ~tail:false) bodies
    | MLcons (_, _, l) | MLtuple l -> List.iter (walk ~tail:false) l
    | MLparray (a, d) ->
      Array.iter (walk ~tail:false) a;
      walk ~tail:false d
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ ->
      ()
  and continuation ~tail = function
    | MLlam _ as k -> walk ~tail (snd (split_params 0 k))
    | k -> walk ~tail:false k
  in
  walk ~tail:true body;
  if !nontail_call then Nontail else if !tail_call then Tail else No_recursion

let combine a b =
  match (a, b) with
  | Nontail, _ | _, Nontail -> Nontail
  | Tail, _ | _, Tail -> Tail
  | No_recursion, No_recursion -> No_recursion

(* A group with partners is planned as one: Loopify inlines the partners
   into a member before reading it, where a tail call to one continues in
   that partner's body and any other call is wrapped in a closure, so the
   calls it then reads are every call between members.  A function on no
   cycle calls no function it could recurse through. *)
let analyze groups struc =
  let defs = ref Ref.User.Map.empty in
  Modutil.struct_iter
    (fun d -> List.iter (fun fd -> defs := Ref.User.Map.add fd.fd_ref fd !defs) (Mlutil.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let defs = !defs in
  let arity fd = fst (split_params 0 fd.fd_body) in
  let kind_of members =
    let arity_of r =
      if List.exists (Common.globref_equal r) members then
        Option.map arity (Ref.User.Map.find_opt r defs)
      else None
    in
    List.fold_left
      (fun k m ->
        match Ref.User.Map.find_opt m defs with
        | Some fd ->
          combine k (classify ~arity_of ~mode:(Core_effects.declaration_mode fd.fd_type) fd.fd_body)
        | None -> k )
      No_recursion members
  in
  let plans =
    List.map (fun members -> {members; kind = kind_of members}) (Recursive_groups.groups groups)
  in
  let by_member =
    List.fold_left
      (fun m g -> List.fold_left (fun m r -> Ref.User.Map.add r g m) m g.members)
      Ref.User.Map.empty plans
  in
  let defined = Ref.User.Map.fold (fun r _ s -> Ref.User.Set.add r s) defs Ref.User.Set.empty in
  (* Every recursive group has exactly one plan, and a function on no cycle
     reads as not recursing. *)
  if Probe.checking () then
    Ref.User.Map.iter
      (fun r _ ->
        let planned = Option.map (fun g -> g.members) (Ref.User.Map.find_opt r by_member) in
        let grouped = Recursive_groups.group groups r in
        let off_cycle_recurses () = kind_of [r] <> No_recursion in
        if (not (Option.equal (List.equal Common.globref_equal) planned grouped))
           || (grouped = None && off_cycle_recurses ())
        then
          Probe.violation "recursion plan"
            Pp.(str "no single plan for the group of " ++ str (Table.kername_of_global r)) )
      defs;
  {groups = plans; by_member; defined}

let equal a b =
  List.equal
    (fun g g' -> List.equal Common.globref_equal g.members g'.members && g.kind = g'.kind)
    a.groups b.groups
  && Ref.User.Set.equal a.defined b.defined

let installed : t ref = State.cell State.Extraction empty

let install t = installed := t

let group_of r = Ref.User.Map.find_opt r !installed.by_member

let find r =
  match group_of r with
  | Some g -> Some g.kind
  | None -> if Ref.User.Set.mem r !installed.defined then Some No_recursion else None
