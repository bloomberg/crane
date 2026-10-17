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

type local_group = {
  origin : Names.GlobRef.t;
  binders : Names.Id.t list;
  local_kind : kind;
}

type t = {
  groups : group list;
  by_member : group Ref.User.Map.t;
  defined : Ref.User.Set.t;
  locals : local_group list;
}

let empty = {groups = []; by_member = Ref.User.Map.empty; defined = Ref.User.Set.empty; locals = []}

let rec split_params n = function
  | MLlam (_, _, b) -> split_params (n + 1) b
  | b -> (n, b)

(* How [fd_body], a function generated in [mode], calls the members of its
   recursive group, as the C++ it becomes does: a call is a tail call where
   its result is the function's, and a call the C++ wraps in a closure, or
   one applied to more arguments than its parameters, is not.  [callee
   ~depth f] is the number of parameters of the member [f] names, under
   [depth] binders inside the function's parameters, and [None] where [f]
   names none. *)
let classify ~callee ~mode fd_body =
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
  let rec walk ~depth ~tail e =
    let walk_under n ~tail e = walk ~depth:(depth + n) ~tail e in
    let walk ~tail e = walk ~depth ~tail e in
    match e with
    | f when callee ~depth f = Some 0 -> if tail then tail_call := true else nontail_call := true
    | MLcons (_, c, [a]) when identity c -> walk ~tail a
    | MLapp (MLglob use, [a]) when identity use.callee && Table.to_inline use.callee -> walk ~tail a
    | MLapp (f, args) when Option.has_some (callee ~depth f) ->
      List.iter (walk ~tail:false) args;
      if tail && Some (List.length args) = callee ~depth f then tail_call := true
      else nontail_call := true
    | MLapp (MLglob use, args) when effect use = Some Core_effects.Bind -> (
      (* The action runs, and the continuation's body goes on where the bind
         stands. *)
      match List.rev args with
      | k :: action :: rest ->
        List.iter (walk ~tail:false) rest;
        walk ~tail:false action;
        continuation ~depth ~tail k
      | _ -> List.iter (walk ~tail:false) args )
    | MLapp (MLglob use, args) when effect use = Some Core_effects.Return -> (
      match List.rev args with
      | value :: rest ->
        List.iter (walk ~tail:false) rest;
        walk ~tail value
      | [] -> () )
    | MLapp ((MLlam _ as f), args) ->
      List.iter (walk ~tail:false) args;
      let rec enter entered n = function
        | MLlam (_, _, b) when n > 0 -> enter (entered + 1) (n - 1) b
        | b -> walk_under entered ~tail:(tail && n = 0) b
      in
      enter 0 (List.length args) f
    | MLapp (f, args) ->
      walk ~tail:false f;
      List.iter (walk ~tail:false) args
    | MLletin (_, _, a, b) ->
      walk ~tail:false a;
      walk_under 1 ~tail b
    | MLcase (_, s, branches) ->
      walk ~tail:false s;
      Array.iter (fun (ids, _, _, b) -> walk_under (List.length ids) ~tail b) branches
    | MLmagic (_, a) -> walk ~tail a
    | MLlam (_, _, b) -> walk_under 1 ~tail:false b
    | MLfix (_, ids, bodies, _) -> Array.iter (walk_under (Array.length ids) ~tail:false) bodies
    | MLcons (_, _, l) | MLtuple l -> List.iter (walk ~tail:false) l
    | MLparray (a, d) ->
      Array.iter (walk ~tail:false) a;
      walk ~tail:false d
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ ->
      ()
  and continuation ~depth ~tail = function
    | MLlam _ as k ->
      let n, b = split_params 0 k in
      walk ~depth:(depth + n) ~tail b
    | k -> walk ~depth ~tail:false k
  in
  walk ~depth:0 ~tail:true body;
  if !nontail_call then Nontail else if !tail_call then Tail else No_recursion

let combine a b =
  match (a, b) with
  | Nontail, _ | _, Nontail -> Nontail
  | Tail, _ | _, Tail -> Tail
  | No_recursion, No_recursion -> No_recursion

(* The plan of every local fixpoint in [defs], one per fixpoint, under the
   definition it occurs in.  Inside a member's body, before its parameters,
   the member [k] of [n] is the variable [n - k]. *)
let local_groups defs =
  let plans = ref [] in
  let plan origin ids funs =
    let n = Array.length ids in
    let arities = Array.map (fun f -> fst (split_params 0 f)) funs in
    let kind_of j =
      let n_params = arities.(j) in
      let rec strip = function MLmagic (_, e) -> strip e | e -> e in
      let callee ~depth f =
        match strip f with
        | MLrel db ->
          let k = n_params + n + depth - db in
          if 0 <= k && k < n then Some arities.(k) else None
        | _ -> None
      in
      classify ~callee ~mode:(Core_effects.declaration_mode (snd ids.(j))) funs.(j)
    in
    let kind = Array.fold_left combine No_recursion (Array.init n kind_of) in
    plans :=
      {origin; binders = Array.to_list (Array.map fst ids); local_kind = kind} :: !plans
  in
  Ref.User.Map.iter
    (fun r fd ->
      let rec visit = function
        | MLfix (_, ids, funs, _) ->
          plan r ids funs;
          Array.iter visit funs
        | e -> Mlutil.ast_iter visit e
      in
      visit fd.fd_body )
    defs;
  List.rev !plans

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
    let callee ~depth:_ = function
      | MLglob use when List.exists (Common.globref_equal use.callee) members ->
        Option.map arity (Ref.User.Map.find_opt use.callee defs)
      | _ -> None
    in
    List.fold_left
      (fun k m ->
        match Ref.User.Map.find_opt m defs with
        | Some fd ->
          combine k (classify ~callee ~mode:(Core_effects.declaration_mode fd.fd_type) fd.fd_body)
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
  {groups = plans; by_member; defined; locals = local_groups defs}

let equal a b =
  List.equal
    (fun g g' -> List.equal Common.globref_equal g.members g'.members && g.kind = g'.kind)
    a.groups b.groups
  && Ref.User.Set.equal a.defined b.defined
  && List.equal
       (fun l l' ->
         Common.globref_equal l.origin l'.origin
         && List.equal Names.Id.equal l.binders l'.binders
         && l.local_kind = l'.local_kind )
       a.locals b.locals

let installed : t ref = State.cell State.Extraction empty

let install t = installed := t

let group_of r = Ref.User.Map.find_opt r !installed.by_member

let find r =
  match group_of r with
  | Some g -> Some g.kind
  | None -> if Ref.User.Set.mem r !installed.defined then Some No_recursion else None

let find_local ~origin ~binder =
  List.fold_left
    (fun found l ->
      if Common.globref_equal l.origin origin && List.exists (Names.Id.equal binder) l.binders then
        Some (combine l.local_kind (Option.default No_recursion found))
      else found )
    None !installed.locals
