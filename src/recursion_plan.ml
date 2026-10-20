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
  occurrence : Occurrence.t;  (* the fixpoint's *)
  local_kind : kind;
  chains : chain list option list;
      (* per member, its chains, if it recurses through no other call that
         is not a tail call *)
  suspends : bool;  (* some member's body suspends ({!suspends_within}) *)
}

(* Where a function goes on once a recursive call returns: the binder the
   call's result is bound to, and the binders bound before it that what
   follows reads, which a frame keeps across the call. *)
type resume = {
  binder : Core_binder.t;
  live : Core_binder.t list;
  calls : Occurrence.t list;  (* the recursive calls of globals it resumes after *)
}

type t = {
  groups : group list;
  by_member : group Ref.User.Map.t;
  defined : Ref.User.Set.t;
  locals : local_group list;
  modulo_cons : chain list Ref.User.Map.t;
  suspended : Ref.User.Set.t;  (* the definitions whose body suspends *)
  resumes : resume list Ref.User.Map.t;
}

let empty =
  { groups = [];
    by_member = Ref.User.Map.empty;
    defined = Ref.User.Set.empty;
    locals = [];
    modulo_cons = Ref.User.Map.empty;
    suspended = Ref.User.Set.empty;
    resumes = Ref.User.Map.empty }

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
    | MLletin (_, _, a, b, _) ->
      walk ~tail:false a;
      walk_under 1 ~tail b
    | MLcase (_, s, branches) ->
      walk ~tail:false s;
      Array.iter (fun (ids, _, _, b) -> walk_under (List.length ids) ~tail b) branches
    | MLmagic (_, a) -> walk ~tail a
    | MLlam (_, _, b) -> walk_under 1 ~tail:false b
    | MLfix (_, ids, bodies, _, _) -> Array.iter (walk_under (Array.length ids) ~tail:false) bodies
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
  | MLletin ((Tmp _ as id), ty, rhs, body, occ) ->
    let rhs = restore_temporaries rhs and body = restore_temporaries body in
    let reads = ref 0 in
    Mlutil.ast_iter_rel_applied (fun n i _ -> if i = n + 1 then incr reads) body;
    if !reads = 1 then Mlutil.ast_subst rhs body else MLletin (id, ty, rhs, body, occ)
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
      | MLletin (_, _, a, b, _) -> calls ~depth a + under 1 b
      | MLlam (_, _, b) -> under 1 b
      | MLcase (_, s, branches) ->
        Array.fold_left
          (fun n (ids, _, _, b) -> n + under (List.length ids) b)
          (calls ~depth s) branches
      | MLfix (_, ids, funs, _, _) -> Array.fold_left (fun n b -> n + under (Array.length ids) b) 0 funs
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
    | MLletin (_, _, a, b, _) ->
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

(* [f lex e'] for [e] and every term [e'] in it, [lex] the lexical
   environment [e'] stands in, [e] standing in [lex]. *)
let rec iter_scoped f lex e =
  f lex e;
  let bind ids lex =
    Lexenv.push
      (List.map
         (fun (x, ty) -> {Lexenv.eb_id = Mlutil.id_of_mlid x; eb_type = ty; eb_role = Lexenv.Value})
         ids )
      lex
  in
  match e with
  | MLlam (x, ty, b) -> iter_scoped f (bind [(x, ty)] lex) b
  | MLletin (x, ty, a, b, _) ->
    iter_scoped f lex a;
    iter_scoped f (bind [(x, ty)] lex) b
  | MLcase (_, s, branches) ->
    iter_scoped f lex s;
    Array.iter (fun (ids, _, _, b) -> iter_scoped f (bind (List.rev ids) lex) b) branches
  | MLfix (_, ids, funs, _, _) ->
    (* The last function of the group is the innermost binder. *)
    let lex = bind (List.rev_map (fun (g, ty) -> (Id g, ty)) (Array.to_list ids)) lex in
    Array.iter (iter_scoped f lex) funs
  | e -> Mlutil.ast_iter (iter_scoped f lex) e

(* Whether [e], standing in [lex] in the definition [self], suspends a
   coinductive constructor ({!Translation_support.suspends_constructor})
   anywhere, under a lambda or in a local fixpoint's body too: the C++ [e]
   becomes holds the suspension wherever it stands. *)
let suspends_within ~self lex e =
  let exception Found in
  try
    iter_scoped
      (fun lex -> function
        | MLcons (Tglob (n, _, _), c, args)
          when (not (Table.is_custom c))
               && Translation_support.suspends_constructor ~self:(Some self)
                    ~binder_type:(Lexenv.type_opt lex) n args ->
          raise Found
        | _ -> () )
      lex e;
    false
  with Found -> true

(* Whether the C++ the definition [self] of type [ty] becomes holds a
   suspension: it is suspended whole
   ({!Translation_support.suspends_whole}), or at a constructor. *)
let definition_suspends self ty body =
  let lex, body = Core_elaborate.declaration_scope ty body in
  Translation_support.suspends_whole self (Ml_type_util.ml_return_type ty) body
  || suspends_within ~self lex body

(* The levels of the binders outside [e] that [e] reads, [e] standing under
   [depth] binders. *)
let free_levels ~depth e =
  let found = ref [] in
  let rec go d = function
    | MLrel i -> if i > d then found := (depth + d - i) :: !found
    | MLlam (_, _, b) -> go (d + 1) b
    | MLletin (_, _, a, b, _) ->
      go d a;
      go (d + 1) b
    | MLcase (_, s, branches) ->
      go d s;
      Array.iter (fun (ids, _, _, b) -> go (d + List.length ids) b) branches
    | MLfix (_, ids, funs, _, _) -> Array.iter (go (d + Array.length ids)) funs
    | e -> Mlutil.ast_iter (go d) e
  in
  go 0 e;
  List.sort_uniq Int.compare !found

(* The points the body of [origin], standing in [lex], resumes at once a
   recursive call returns: a let whose right-hand side is the call, or ends
   in one in some branch, and a sequential bind whose action is the call,
   its continuation's parameter binding the result.  In the body itself a
   recursive call is one [calls] recognises; in a local fixpoint's bodies it
   is a call of a member of that fixpoint, or of an enclosing group, whose
   machine Loopify may make the fixpoint a second entry of.  A call under a
   lambda is made where the closure runs, not here. *)
let resumes_of ~effects ~origin ~calls lex body =
  let effect = sequential effects in
  let found = ref [] in
  let binder level = Core_binder.make ~origin ~level () in
  let resume ?(calls = []) ~site depth rest =
    let live = List.filter (fun l -> l <> depth) (free_levels ~depth:(depth + 1) rest) in
    found :=
      {binder = Core_binder.make ~origin ~level:depth ~site (); live = List.map binder live; calls}
      :: !found
  in
  let rec occurrence = function
    | MLmagic (_, e) -> occurrence e
    | MLapp (MLglob use, _) -> [Global_use.occurrence use]
    | _ -> []
  in
  let rec walk ~calls depth e =
    (* A local fixpoint applied where it is written, reaching a recursive
       call, is bound as one ({!Normalize}). *)
    let rec reaches depth e =
      calls ~depth e
      ||
      match e with
      | MLfix (_, ids, funs, _, _) ->
        Array.exists
          (fun f ->
            let arity, b = split_params 0 f in
            reaches (depth + Array.length ids + arity) b )
          funs
      | MLlam _ -> false
      | MLletin (_, _, a, b, _) -> reaches depth a || reaches (depth + 1) b
      | MLcase (_, s, branches) ->
        reaches depth s
        || Array.exists (fun (ids, _, _, b) -> reaches (depth + List.length ids) b) branches
      | e ->
        let found = ref false in
        Mlutil.ast_iter (fun c -> if reaches depth c then found := true) e;
        !found
    in
    let rec ends_in_call depth e =
      calls ~depth e
      ||
      match e with
      | MLapp ((MLfix _ as fix), _) -> reaches depth fix
      | MLcase (_, _, branches) ->
        Array.exists (fun (ids, _, _, b) -> ends_in_call (depth + List.length ids) b) branches
      | MLletin (_, _, _, b, _) -> ends_in_call (depth + 1) b
      | MLmagic (_, b) -> ends_in_call depth b
      | _ -> false
    in
    (* The calls of globals a right-hand side ends in. *)
    let rec ending_calls depth e =
      if calls ~depth e then occurrence e
      else
        match e with
        | MLcase (_, _, branches) ->
          List.concat_map
            (fun (ids, _, _, b) -> ending_calls (depth + List.length ids) b)
            (Array.to_list branches)
        | MLletin (_, _, _, b, _) -> ending_calls (depth + 1) b
        | MLmagic (_, b) -> ending_calls depth b
        | _ -> []
    in
    let go = walk ~calls in
    match e with
    | MLletin (_, _, a, b, site) ->
      if ends_in_call depth a then resume ~calls:(ending_calls depth a) ~site depth b;
      go depth a;
      go (depth + 1) b
    | MLapp (MLglob use, args) when effect use = Some Core_effects.Bind -> (
      match List.rev args with
      | MLlam (_, _, k) :: action :: rest ->
        if calls ~depth action then
          resume ~calls:(occurrence action) ~site:(Global_use.occurrence use) depth k;
        List.iter (go depth) (action :: rest);
        go (depth + 1) k
      | _ -> List.iter (go depth) args )
    | MLcase (_, s, branches) ->
      go depth s;
      Array.iter (fun (ids, _, _, b) -> go (depth + List.length ids) b) branches
    | MLfix (_, ids, funs, _, _) ->
      (* The member [m] is bound at level [depth + m], the last innermost. *)
      let first = depth and n = Array.length ids in
      let rec member ~depth = function
        | MLmagic (_, e) -> member ~depth e
        | MLapp (MLrel k, _) -> first <= depth - k && depth - k < first + n
        | _ -> false
      in
      Array.iter
        (fun f ->
          let arity, b = split_params 0 f in
          walk ~calls:(fun ~depth e -> member ~depth e || calls ~depth e) (depth + n + arity) b )
        funs
    | MLlam _ -> ()
    | e -> Mlutil.ast_iter (go depth) e
  in
  walk ~calls:(fun ~depth:_ e -> calls e) (Lexenv.depth lex) body;
  List.rev !found

(* The plan of every local fixpoint in [defs], one per fixpoint, under its
   occurrence.  Inside a member's body, before its parameters,
   the member [k] of [n] is the variable [n - k]. *)
let local_groups ~effects defs =
  let plans = ref [] in
  let plan origin lex ids funs occurrence =
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
    let suspends =
      let lex =
        Lexenv.push
          (List.rev_map
             (fun (g, ty) -> {Lexenv.eb_id = g; eb_type = ty; eb_role = Lexenv.Value})
             (Array.to_list ids) )
          lex
      in
      Array.exists (suspends_within ~self:origin lex) funs
    in
    plans :=
      { occurrence;
        local_kind = kind;
        chains;
        suspends }
      :: !plans
  in
  Ref.User.Map.iter
    (fun r fd ->
      let lex, body = Core_elaborate.declaration_scope fd.fd_type fd.fd_body in
      iter_scoped
        (fun lex -> function MLfix (_, ids, funs, _, occ) -> plan r lex ids funs occ | _ -> ())
        lex body )
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
  let suspended =
    Ref.User.Map.fold
      (fun r fd s ->
        if definition_suspends r fd.fd_type fd.fd_body then Ref.User.Set.add r s else s )
      defs Ref.User.Set.empty
  in
  (* A definition off every group that does not recurse only by tail calls
     resumes nowhere but in its local fixpoints. *)
  let resumes =
    Ref.User.Map.mapi
      (fun r fd ->
        let members =
          match Ref.User.Map.find_opt r by_member with
          | Some g when g.kind = Nontail -> g.members
          | Some _ | None -> []
        in
        let rec calls = function
          | MLmagic (_, e) -> calls e
          | MLapp (MLglob use, _) -> List.exists (Common.globref_equal use.callee) members
          | _ -> false
        in
        let lex, body = Core_elaborate.generated_scope fd.fd_type fd.fd_body in
        resumes_of ~effects ~origin:r ~calls lex body )
      defs
  in
  { groups = plans;
    by_member;
    defined;
    locals = local_groups ~effects defs;
    modulo_cons;
    suspended;
    resumes }

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
         Occurrence.equal l.occurrence l'.occurrence
         && l.local_kind = l'.local_kind
         && List.equal (Option.equal same_chains) l.chains l'.chains
         && l.suspends = l'.suspends )
       a.locals b.locals
  && Ref.User.Map.equal same_chains a.modulo_cons b.modulo_cons
  && Ref.User.Set.equal a.suspended b.suspended
  && Ref.User.Map.equal
       (List.equal (fun r r' ->
            Core_binder.equal r.binder r'.binder
            && Core_binder.same_site r.binder r'.binder
            && List.equal Core_binder.equal r.live r'.live
            && List.equal Occurrence.equal r.calls r'.calls ) )
       a.resumes b.resumes

let installed : t ref = State.cell State.Extraction empty

let install t = installed := t

let group_of r = Ref.User.Map.find_opt r !installed.by_member

type strategy =
  | No_loop
  | Tail_loop
  | Modulo_cons of chain list
  | Frame_stack
  | Suspended of kind

let kind_of_strategy = function
  | No_loop -> No_recursion
  | Tail_loop -> Tail
  | Modulo_cons _ | Frame_stack -> Nontail
  | Suspended kind -> kind

(* The strategy of a function of kind [kind] whose chains are [chains], in a
   group some member of which suspends where [suspends]: tail modulo cons
   where there is a chain, every one ends in the same cell, whose hole its
   constructor stores behind the pointer, and every constructor in them
   stores some field there. *)
let strategy_of ~pointer_fields ~suspends kind chains =
  match (kind, chains) with
  | No_recursion, _ -> No_loop
  | (Tail | Nontail), _ when suspends -> Suspended kind
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

(* A partner is inlined into a member, its suspensions with it. *)
let strategy ~pointer_fields r =
  if Ref.User.Set.mem r !installed.defined then
    let kind, members =
      match group_of r with Some g -> (g.kind, g.members) | None -> (No_recursion, [r])
    in
    let suspends = List.exists (fun m -> Ref.User.Set.mem m !installed.suspended) members in
    Some
      (strategy_of ~pointer_fields ~suspends kind (Ref.User.Map.find_opt r !installed.modulo_cons))
  else None

(* One strategy for two plans of what is lowered as one function. *)
let both a b =
  match (a, b) with
  | Suspended k, s | s, Suspended k -> Suspended (combine k (kind_of_strategy s))
  | Modulo_cons (c :: _ as cs), Modulo_cons (c' :: _ as cs')
    when same_cell c.innermost c'.innermost ->
    Modulo_cons (cs @ cs')
  | (Modulo_cons _ | Frame_stack), _ | _, (Modulo_cons _ | Frame_stack) -> Frame_stack
  | Tail_loop, _ | _, Tail_loop -> Tail_loop
  | No_loop, No_loop -> No_loop

(* A copy of a fixpoint keeps its occurrence, so a definition holding two
   copies plans it twice: the copies are lowered by one strategy. *)
let strategy_at ~pointer_fields (occurrence, member) =
  List.fold_left
    (fun found l ->
      if Occurrence.equal l.occurrence occurrence then
        match List.nth_opt l.chains member with
        | Some chains ->
          let this = strategy_of ~pointer_fields ~suspends:l.suspends l.local_kind chains in
          Some (match found with Some f -> both f this | None -> this)
        | None -> found
      else found )
    None !installed.locals

let resumes_binding (b : Core_binder.t) =
  match Ref.User.Map.find_opt b.origin !installed.resumes with
  | Some rs -> List.filter (fun r -> Core_binder.equal r.binder b && Core_binder.same_site r.binder b) rs
  | None -> []
