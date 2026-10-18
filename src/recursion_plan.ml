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

(* A constructor applied around a recursive call: the argument at [hole]
   holds the call. *)
type cell = {
  constructor : Names.GlobRef.t;
  hole : int;
}

(* The constructors around one recursive call, outermost first, the
   innermost holding the call itself. *)
type chain = {
  around : cell list;
  innermost : cell;
}

type local_group = {
  origin : Names.GlobRef.t;
  binders : Names.Id.t list;
  local_kind : kind;
  chains : chain list option list;
      (* per binder, its chains, if it recurses through no other call that
         is not a tail call *)
}

type t = {
  groups : group list;
  by_member : group Ref.User.Map.t;
  defined : Ref.User.Set.t;
  locals : local_group list;
  modulo_cons : chain list Ref.User.Map.t;
}

let empty =
  { groups = [];
    by_member = Ref.User.Map.empty;
    defined = Ref.User.Set.empty;
    locals = [];
    modulo_cons = Ref.User.Map.empty }

let rec split_params n = function
  | MLlam (_, _, b) -> split_params (n + 1) b
  | b -> (n, b)

(* The effect operation [use] is, where [effects] says it is generated
   sequentially: a bind's continuation and a ret's value then stand where
   the operation does. *)
let sequential effects use =
  match Core_effects.lookup effects use with
  | Some {Core_effects.operation; mode = Core_effects.Sequential} -> Some operation
  | Some _ | None -> None

(* A custom whose replacement text is its one argument writes nothing
   around it, so the argument is where the custom is: sequential [itree]
   maps [go] and [TauF] so, and [Tau t] is [t]. *)
let identity r =
  Table.is_custom r && Minicpp.inline_shape_of_text (Table.find_custom r) = Minicpp.Inline_identity

(* How [fd_body] calls the members of its recursive group, as the C++ it
   becomes does: a call is a tail call where its result is the function's,
   and a call the C++ wraps in a closure, or one applied to more arguments
   than its parameters, is not.  [callee ~depth f] is the number of
   parameters of the member [f] names, under [depth] binders inside the
   function's parameters, and [None] where [f] names none.  A bind or a ret
   is sequencing where [effects], the analysis of the program [fd_body] is
   taken from, says it is generated sequentially. *)
let classify ~effects ~callee fd_body =
  let _, body = split_params 0 fd_body in
  let tail_call = ref false and nontail_call = ref false in
  let effect = sequential effects in
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

(* [e] with each temporary {!Normalize} bound a call to put back where it
   is read, when it is read once: the expression Normalize took the call out
   of, as {!Cpp_temporaries} restores it for the transform that reads
   constructors around calls. *)
let rec restore_temporaries e =
  match e with
  | MLletin ((Tmp _ as id), ty, rhs, body) ->
    let rhs = restore_temporaries rhs and body = restore_temporaries body in
    let reads = ref 0 in
    Mlutil.ast_iter_rel_applied (fun n i _ -> if i = n + 1 then incr reads) body;
    if !reads = 1 then Mlutil.ast_subst rhs body else MLletin (id, ty, rhs, body)
  | e -> Mlutil.ast_map restore_temporaries e

(* The constructor chains the member [self] of a recursive group builds its
   result of, if it recurses only through tail calls and through calls that
   are each the one call of a chain in tail position, one chain per call:
   constructor applications each holding the call in one of its arguments,
   the innermost holding it directly.  [bodies.(k)] is the member [k]'s
   body, parameters included, read with Normalize's temporaries put back,
   and [member ~within ~depth f] the member [f] names in the body of the
   member [within], under [depth] binders inside its parameters.  A tail call to a partner continues in
   the partner's body, as Loopify inlines it there; any other call to a
   partner is inlined in a closure, out of reach.  A partner already
   inlined is called as any function is. *)
let modulo_cons_chains ~effects ~member ~bodies self =
  let bodies = Array.map (fun b -> split_params 0 (restore_temporaries b)) bodies in
  let effect = sequential effects in
  let chains = ref [] and general = ref false in
  let general_if b = if b then general := true in
  let rec walk ~within ~inlined ~depth e =
    let reached ~depth f =
      match member ~within ~depth f with
      | Some k when not (List.mem k inlined) -> Some k
      | Some _ | None -> None
    in
    let rec calls ~depth e =
      let under n = calls ~depth:(depth + n) in
      match e with
      | MLapp (f, args) when Option.has_some (reached ~depth f) ->
        List.fold_left (fun n a -> n + calls ~depth a) 1 args
      | f when Option.has_some (reached ~depth f) -> 1
      | MLletin (_, _, a, b) -> calls ~depth a + under 1 b
      | MLlam (_, _, b) -> under 1 b
      | MLcase (_, s, branches) ->
        Array.fold_left
          (fun n (ids, _, _, b) -> n + under (List.length ids) b)
          (calls ~depth s) branches
      | MLfix (_, ids, funs, _) -> Array.fold_left (fun n b -> n + under (Array.length ids) b) 0 funs
      | e ->
        let n = ref 0 in
        Mlutil.ast_iter (fun c -> n := !n + calls ~depth c) e;
        !n
    in
    let full_call ~depth = function
      | MLapp (f, args) -> (
        match reached ~depth f with
        | Some k
          when fst bodies.(k) = List.length args && List.for_all (fun a -> calls ~depth a = 0) args
          ->
          Some k
        | Some _ | None -> None )
      | _ -> None
    in
    let self_call ~depth e = full_call ~depth e = Some self in
    let rec chain = function
      | MLcons (_, constructor, args) -> (
        let args = List.mapi (fun hole a -> (hole, a)) args in
        match List.filter (fun (_, a) -> self_call ~depth a) args with
        | [(hole, _)] -> Some {around = []; innermost = {constructor; hole}}
        | [] -> (
          match List.filter (fun (_, a) -> calls ~depth a = 1) args with
          | [(hole, a)] ->
            Option.map (fun c -> {c with around = {constructor; hole} :: c.around}) (chain a)
          | _ -> None )
        | _ -> None )
      | _ -> None
    in
    let walk_under n e = walk ~within ~inlined ~depth:(depth + n) e in
    match e with
    | MLcase (_, s, branches) ->
      general_if (calls ~depth s > 0);
      Array.iter (fun (ids, _, _, b) -> walk_under (List.length ids) b) branches
    | MLletin (_, _, a, b) ->
      general_if (calls ~depth a > 0);
      walk_under 1 b
    | MLmagic (_, a) -> general_if ((not (self_call ~depth a)) && calls ~depth a > 0)
    | MLcons (_, c, [a]) when identity c -> walk_under 0 a
    | MLapp (MLglob use, [a]) when identity use.callee && Table.to_inline use.callee -> walk_under 0 a
    | MLapp (MLglob use, args) when effect use = Some Core_effects.Bind -> (
      match List.rev args with
      | (MLlam _ as k) :: action :: rest ->
        general_if (List.exists (fun a -> calls ~depth a > 0) (action :: rest));
        let n, b = split_params 0 k in
        walk_under n b
      | _ -> general_if (calls ~depth e > 0) )
    | MLapp (MLglob use, args) when effect use = Some Core_effects.Return -> (
      match List.rev args with
      | value :: rest ->
        general_if (List.exists (fun a -> calls ~depth a > 0) rest);
        walk_under 0 value
      | [] -> () )
    | _ when self_call ~depth e -> ()
    | _ -> (
      match full_call ~depth e with
      | Some partner ->
        walk ~within:partner ~inlined:(partner :: inlined) ~depth:0 (snd bodies.(partner))
      | None -> (
        match calls ~depth e with
        | 0 -> ()
        | 1 -> ( match chain e with Some c -> chains := c :: !chains | None -> general := true )
        | _ -> general := true ) )
  in
  walk ~within:self ~inlined:[] ~depth:0 (snd bodies.(self));
  if !general then None else Some (List.rev !chains)

(* The plan of every local fixpoint in [defs], one per fixpoint, under the
   definition it occurs in.  Inside a member's body, before its parameters,
   the member [k] of [n] is the variable [n - k]. *)
let local_groups ~effects defs =
  let plans = ref [] in
  let plan origin ids funs =
    let n = Array.length ids in
    let arities = Array.map (fun f -> fst (split_params 0 f)) funs in
    let rec strip = function MLmagic (_, e) -> strip e | e -> e in
    let member ~within ~depth f =
      match strip f with
      | MLrel db ->
        let k = arities.(within) + n + depth - db in
        if 0 <= k && k < n then Some k else None
      | _ -> None
    in
    let kind_of j =
      let callee ~depth f = Option.map (Array.get arities) (member ~within:j ~depth f) in
      classify ~effects ~callee funs.(j)
    in
    let kind = Array.fold_left combine No_recursion (Array.init n kind_of) in
    let chains =
      List.init n (fun j ->
          if kind = Nontail then modulo_cons_chains ~effects ~member ~bodies:funs j else None )
    in
    plans :=
      {origin; binders = Array.to_list (Array.map fst ids); local_kind = kind; chains} :: !plans
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
  let effects = Core_effects.analyze struc in
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
          combine k (classify ~effects ~callee fd.fd_body)
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
  let modulo_cons =
    List.fold_left
      (fun m g ->
        if g.kind <> Nontail then m
        else
          let index r =
            let rec go k = function
              | [] -> None
              | m :: ms -> if Common.globref_equal m r then Some k else go (k + 1) ms
            in
            go 0 g.members
          in
          let bodies =
            Array.of_list (List.map (fun r -> (Ref.User.Map.find r defs).fd_body) g.members)
          in
          let member ~within:_ ~depth:_ = function MLglob use -> index use.callee | _ -> None in
          let chains_of r = Option.bind (index r) (modulo_cons_chains ~effects ~member ~bodies) in
          List.fold_left
            (fun m r ->
              match chains_of r with Some chains -> Ref.User.Map.add r chains m | None -> m )
            m g.members )
      Ref.User.Map.empty plans
  in
  {groups = plans; by_member; defined; locals = local_groups ~effects defs; modulo_cons}

let same_cell c c' = Common.globref_equal c.constructor c'.constructor && c.hole = c'.hole

let same_chains =
  List.equal (fun c c' ->
      List.equal same_cell c.around c'.around && same_cell c.innermost c'.innermost )

let equal a b =
  List.equal
    (fun g g' -> List.equal Common.globref_equal g.members g'.members && g.kind = g'.kind)
    a.groups b.groups
  && Ref.User.Set.equal a.defined b.defined
  && List.equal
       (fun l l' ->
         Common.globref_equal l.origin l'.origin
         && List.equal Names.Id.equal l.binders l'.binders
         && l.local_kind = l'.local_kind
         && List.equal (Option.equal same_chains) l.chains l'.chains )
       a.locals b.locals
  && Ref.User.Map.equal same_chains a.modulo_cons b.modulo_cons

let installed : t ref = State.cell State.Extraction empty

let install t = installed := t

let group_of r = Ref.User.Map.find_opt r !installed.by_member

type strategy =
  | No_loop
  | Tail_loop
  | Modulo_cons of chain list
  | Frame_stack

let kind_of_strategy = function
  | No_loop -> No_recursion
  | Tail_loop -> Tail
  | Modulo_cons _ | Frame_stack -> Nontail

(* The strategy of a function of kind [kind] whose chains are [chains]:
   tail modulo cons where there is a chain, every one ends in the same cell,
   whose hole its constructor stores behind the pointer, and every
   constructor in them stores some field there. *)
let strategy_of ~pointer_fields kind chains =
  match (kind, chains) with
  | No_recursion, _ -> No_loop
  | Tail, _ -> Tail_loop
  | Nontail, Some ({innermost; _} :: _ as chains)
    when (let stored c = pointer_fields c.constructor in
          (match stored innermost with Some fields -> List.mem innermost.hole fields | None -> false)
          && List.for_all
               (fun c ->
                 same_cell c.innermost innermost
                 && List.for_all (fun c -> Option.has_some (stored c)) (c.innermost :: c.around) )
               chains ) ->
    Modulo_cons chains
  | Nontail, _ -> Frame_stack

let strategy ~pointer_fields r =
  if Ref.User.Set.mem r !installed.defined then
    let kind = match group_of r with Some g -> g.kind | None -> No_recursion in
    Some (strategy_of ~pointer_fields kind (Ref.User.Map.find_opt r !installed.modulo_cons))
  else None

let strategy_local ~pointer_fields ~origin ~binder =
  let both a b =
    match (a, b) with
    | Modulo_cons (c :: _ as cs), Modulo_cons (c' :: _ as cs')
      when same_cell c.innermost c'.innermost ->
      Modulo_cons (cs @ cs')
    | (Modulo_cons _ | Frame_stack), _ | _, (Modulo_cons _ | Frame_stack) -> Frame_stack
    | Tail_loop, _ | _, Tail_loop -> Tail_loop
    | No_loop, No_loop -> No_loop
  in
  List.fold_left
    (fun found l ->
      if Common.globref_equal l.origin origin then
        List.fold_left2
          (fun found b chains ->
            if Names.Id.equal b binder then
              let this = strategy_of ~pointer_fields l.local_kind chains in
              Some (match found with Some f -> both f this | None -> this)
            else found )
          found l.binders l.chains
      else found )
    None !installed.locals
