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
  adoptable : Occurrence.t list list;  (* per member, {!flow_fixpoints} calling the group *)
  calls : Occurrence.t list list;
      (* per member, the reads heading its calls in the group's bodies *)
}

(* The calls of one partner a function inlines: those that continue in the
   partner's body, and those that run it in their place. *)
type inlining = {
  partner : Names.GlobRef.t;
  continued : Occurrence.t list;
  invoked : Occurrence.t list;
}

(* A call a function resumes after. *)
type target =
  | Function of Names.GlobRef.t
  | Member of Occurrence.t * int
  | Entering of Occurrence.t

(* A call a function resumes after, and the occurrence it is made of: the
   global's use, the read of the member at its head, or the fixpoint
   applied. *)
type call = {
  target : target;
  occurrence : Occurrence.t;
}

(* Where a function goes on once a recursive call returns: the binder the
   call's result is bound to, the binders bound before it that what follows
   reads, which a frame keeps across the call, and the calls it resumes
   after. *)
type resume = {
  binder : Core_binder.t;
  live : Core_binder.t list;
  after : call list;
}

type t = {
  groups : group list;
  by_member : group Ref.User.Map.t;
  defined : Ref.User.Set.t;
  locals : local_group list;
  modulo_cons : chain list Ref.User.Map.t;
  suspended : Ref.User.Set.t;  (* the definitions whose body suspends *)
  resumes : resume list Ref.User.Map.t;
  adoptable : Occurrence.t list Ref.User.Map.t;
  inlinings : inlining list Ref.User.Map.t;
  adopted_invocations : Occurrence.t list Ref.User.Map.t;
  kinds : kind Ref.User.Map.t;  (* per definition, its own calls *)
  let_lambdas : Occurrence.t list;  (* the lets binding a lambda *)
}

let empty =
  { groups = [];
    by_member = Ref.User.Map.empty;
    defined = Ref.User.Set.empty;
    locals = [];
    modulo_cons = Ref.User.Map.empty;
    suspended = Ref.User.Set.empty;
    resumes = Ref.User.Map.empty;
    adoptable = Ref.User.Map.empty;
    inlinings = Ref.User.Map.empty;
    adopted_invocations = Ref.User.Map.empty;
    kinds = Ref.User.Map.empty;
    let_lambdas = [] }

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

(* A partner's body Loopify inlines at a call: continued where the call
   was, or run in a lambda invoked in its place. *)
type inlined_body =
  | Continues of ml_ast
  | Invokes of ml_ast

(* How [body], a function's body inside its parameters, calls the members
   of its recursive group, as the C++ it becomes does: a call is a tail call
   where its result is the function's, and one applied to more arguments
   than its parameters is not.  A call in a closure the body builds -- a
   lambda's body, or a member applied to fewer arguments than its
   parameters, which the C++ makes a closure of -- is made where the
   closure runs, not here: no loop of this function can take it.
   [callee ~depth f] is the number of parameters of the member [f] names,
   under [depth] binders inside the function's parameters, and [None] where
   [f] names none.  A bind or a ret is sequencing where [effects], the
   analysis of the program [body] is taken from, says it is generated
   sequentially.  [inlined use] is the body of a partner Loopify inlines at
   the call [use] heads ({!inlinings_of}), which is read in its place: a
   body continued where the call was, and one invoked as an operand, where
   nothing more is inlined. *)
let classify ?(inlined = fun _ -> None) ~effects ~callee body =
  let tail_call = ref false and nontail_call = ref false in
  let effect_ = sequential effects in
  let rec walk ~inlining ~depth ~tail e =
    let walk_under n ~tail e = walk ~inlining ~depth:(depth + n) ~tail e in
    let walk ~tail e = walk ~inlining ~depth ~tail e in
    let continuation = continuation ~inlining in
    match e with
    | f when callee ~depth f = Some 0 -> if tail then tail_call := true else nontail_call := true
    | MLapp (MLglob use, args) when inlining && Option.has_some (inlined use) -> (
      List.iter (walk ~tail:false) args;
      match inlined use with
      | Some (Continues b) -> walk ~tail b
      | Some (Invokes b) -> walk_body ~inlining:false ~tail:false b
      | None -> () )
    | MLcons (_, c, [a]) when identity c -> walk ~tail a
    | MLapp (MLglob use, [a]) when identity use.callee && Table.to_inline use.callee -> walk ~tail a
    | MLapp (f, args) when Option.has_some (callee ~depth f) ->
      List.iter (walk ~tail:false) args;
      let n = List.length args and parameters = Option.get (callee ~depth f) in
      if n < parameters then ()
      else if tail && n = parameters then tail_call := true
      else nontail_call := true
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      (* The action runs, and the continuation's body goes on where the bind
         stands. *)
      match List.rev args with
      | k :: action :: rest ->
        List.iter (walk ~tail:false) rest;
        walk ~tail:false action;
        continuation ~depth ~tail k
      | _ -> List.iter (walk ~tail:false) args )
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Return -> (
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
    | MLlam _ -> ()
    | MLfix (_, ids, bodies, _, _) ->
      Array.iter
        (fun f ->
          let n, b = split_params 0 f in
          walk_under (Array.length ids + n) ~tail:false b )
        bodies
    | MLcons (_, _, l) | MLtuple l -> List.iter (walk ~tail:false) l
    | MLparray (a, d) ->
      Array.iter (walk ~tail:false) a;
      walk ~tail:false d
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ ->
      ()
  and continuation ~inlining ~depth ~tail = function
    | MLlam _ as k ->
      let n, b = split_params 0 k in
      walk ~inlining ~depth:(depth + n) ~tail b
    | k -> walk ~inlining ~depth ~tail:false k
  and walk_body ~inlining ~tail b = walk ~inlining ~depth:0 ~tail b in
  walk ~inlining:true ~depth:0 ~tail:true body;
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
  let effect_ = sequential effects in
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
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      match List.rev args with
      | (MLlam _ as k) :: action :: rest ->
        general_if (List.exists (fun a -> calls ~depth a > 0) (action :: rest));
        let n, b = split_params 0 k in
        walk_under n b
      | _ -> general_if (calls ~depth e > 0) )
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Return -> (
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
    | MLrel (i, _) -> if i > d then found := (depth + d - i) :: !found
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

(* Whether translation generates a match standing as a let's right-hand
   side as statements, each branch assigning the binder -- a custom match,
   or a record's -- rather than in a lambda invoked in place, as it does
   any other. *)
let match_bound_in_place ty branches =
  Table.is_custom_match branches || (Table.record_fields_of_type ty <> [] && Array.length branches = 1)

(* The points the body of [origin], standing in [lex], resumes at once a
   recursive call returns: a let whose right-hand side is the call, or ends
   in one in some branch, and a sequential bind whose action is the call,
   its continuation's parameter binding the result.  In the body itself a
   recursive call is one [targets] names; in a local fixpoint's bodies a
   call of a member of that fixpoint is one too.  A call under a lambda is
   made where the closure runs, not here. *)
let resumes_of ~effects ~origin ~targets lex body =
  let effect_ = sequential effects in
  let found = ref [] in
  let binder level = Core_binder.make ~origin ~level () in
  let resume ~site ~after depth rest =
    let live = List.filter (fun l -> l <> depth) (free_levels ~depth:(depth + 1) rest) in
    found :=
      {binder = Core_binder.make ~origin ~level:depth ~site (); live = List.map binder live; after}
      :: !found
  in
  let rec walk ~targets depth e =
    (* A local fixpoint applied where it is written, reaching a recursive
       call, is bound as one ({!Normalize}). *)
    let rec reaches depth e =
      targets ~depth e <> []
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
    (* What a right-hand side ends in: the recursive calls its branches end
       in, and a local fixpoint applied there that reaches one.  A match
       ends in its branches' only where they assign the binder; any other is
       run in a lambda, and the right-hand side ends in that lambda's
       invocation. *)
    let rec ending depth e =
      match targets ~depth e with
      | _ :: _ as called -> called
      | [] -> (
        match e with
        | MLapp ((MLfix (_, _, _, _, occ) as fix), _) when reaches depth fix ->
          [{target = Entering occ; occurrence = occ}]
        | MLcase (ty, _, branches) when match_bound_in_place ty branches ->
          List.concat_map
            (fun (ids, _, _, b) -> ending (depth + List.length ids) b)
            (Array.to_list branches)
        | MLletin (_, _, _, b, _) -> ending (depth + 1) b
        | MLmagic (_, b) -> ending depth b
        | _ -> [] )
    in
    let go = walk ~targets in
    match e with
    | MLletin (_, _, a, b, site) ->
      (match ending depth a with [] -> () | after -> resume ~site ~after depth b);
      go depth a;
      go (depth + 1) b
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      match List.rev args with
      | MLlam (_, _, k) :: action :: rest ->
        ( match targets ~depth action with
        | [] -> ()
        | after -> resume ~site:(Global_use.occurrence use) ~after depth k );
        List.iter (go depth) (action :: rest);
        go (depth + 1) k
      | _ -> List.iter (go depth) args )
    | MLcase (_, s, branches) ->
      go depth s;
      Array.iter (fun (ids, _, _, b) -> go (depth + List.length ids) b) branches
    | MLfix (_, ids, funs, _, occ) ->
      (* The member [m] is bound at level [depth + m], the last innermost. *)
      let first = depth and n = Array.length ids in
      let rec member ~depth = function
        | MLmagic (_, e) -> member ~depth e
        | MLapp (MLrel (k, read), _) when first <= depth - k && depth - k < first + n ->
          [{target = Member (occ, depth - k - first); occurrence = read}]
        | _ -> []
      in
      let targets ~depth e = match member ~depth e with [] -> targets ~depth e | called -> called in
      Array.iter
        (fun f ->
          let arity, b = split_params 0 f in
          walk ~targets (depth + n + arity) b )
        funs
    | MLlam _ -> ()
    | e -> Mlutil.ast_iter (go depth) e
  in
  walk ~targets:(fun ~depth:_ e -> targets e) (Lexenv.depth lex) body;
  List.rev !found

(* The local fixpoints in the flow of [body], standing under [depth]
   binders -- run where the code made of [body] runs, not under a lambda nor
   in another local fixpoint -- some member of which names a function
   [names ~depth] recognises, in the order they are met. *)
let flow_fixpoints ~names depth body =
  let rec mentions depth e =
    names ~depth e
    ||
    match e with
    | MLlam (_, _, b) -> mentions (depth + 1) b
    | MLletin (_, _, a, b, _) -> mentions depth a || mentions (depth + 1) b
    | MLcase (_, s, branches) ->
      mentions depth s
      || Array.exists (fun (ids, _, _, b) -> mentions (depth + List.length ids) b) branches
    | MLfix (_, ids, funs, _, _) -> Array.exists (mentions (depth + Array.length ids)) funs
    | e ->
      let found = ref false in
      Mlutil.ast_iter (fun c -> if mentions depth c then found := true) e;
      !found
  in
  let found = ref [] in
  let rec flow depth = function
    | MLfix (_, ids, funs, _, occ) ->
      if Array.exists (mentions (depth + Array.length ids)) funs then found := occ :: !found
    | MLlam _ -> ()
    | MLletin (_, _, a, b, _) ->
      flow depth a;
      flow (depth + 1) b
    | MLcase (_, s, branches) ->
      flow depth s;
      Array.iter (fun (ids, _, _, b) -> flow (depth + List.length ids) b) branches
    | e -> Mlutil.ast_iter (flow depth) e
  in
  flow depth body;
  List.rev !found

(* [f depth e'] for [e] and every term [e'] in it, under [depth] binders
   more than [e]. *)
let rec iter_under f depth e =
  f depth e;
  match e with
  | MLlam (_, _, b) -> iter_under f (depth + 1) b
  | MLletin (_, _, a, b, _) ->
    iter_under f depth a;
    iter_under f (depth + 1) b
  | MLcase (_, s, branches) ->
    iter_under f depth s;
    Array.iter (fun (ids, _, _, b) -> iter_under f (depth + List.length ids) b) branches
  | MLfix (_, ids, funs, _, _) -> Array.iter (iter_under f (depth + Array.length ids)) funs
  | e -> Mlutil.ast_iter (iter_under f depth) e

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
      | MLrel (db, _) ->
        let k = arities.(within) + n + depth - db in
        if 0 <= k && k < n then Some k else None
      | _ -> None
    in
    let kind_of j =
      let callee ~depth f = Option.map (Array.get arities) (member ~within:j ~depth f) in
      classify ~effects ~callee (snd (split_params 0 funs.(j)))
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
    let adoptable =
      List.init n (fun j ->
          let names ~depth = function
            | MLrel _ as read -> Option.has_some (member ~within:j ~depth:(depth - arities.(j)) read)
            | _ -> false
          in
          let arity, body = split_params 0 funs.(j) in
          flow_fixpoints ~names arity body )
    in
    let calls =
      let found = Array.make n [] in
      Array.iteri
        (fun j f ->
          iter_under
            (fun depth -> function
              | MLapp (head, _) -> (
                match (member ~within:j ~depth head, strip head) with
                | Some k, MLrel (_, read) -> found.(k) <- read :: found.(k)
                | _ -> () )
              | _ -> () )
            0
            (snd (split_params 0 f)) )
        funs;
      Array.to_list found
    in
    plans :=
      { occurrence;
        local_kind = kind;
        chains;
        suspends;
        adoptable;
        calls }
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

(* Where a term stands in the C++ translation makes of a body: a statement
   whose value the function returns, a statement whose value is bound or
   dropped, an operand of an expression, or the expression a statement
   returns as it is. *)
type position =
  | Returning
  | Binding
  | Operand
  | Returned

(* A partner's call inlined, and whether it continues in the partner's
   body. *)
type inlined_call = {
  callee : Names.GlobRef.t;
  continues : bool;
  made_of : Occurrence.t;
}

(* The partners' calls [inlines] names that run in [body] as translation
   generates it, the body of the function [self], in the order Loopify
   meets them: [continued] holds the calls an earlier partner's inlining
   continued in, whose arguments are bound and whose callee's body runs in
   their place.  A call runs there unless it stands in a lambda: a
   closure's body, a local fixpoint's, a suspended coinductive constructor's
   arguments or a body suspended whole, and a match, let, fixpoint or bind
   that is an operand, which translation runs in a lambda invoked in place,
   as it does a match bound by a let that is no custom or record match.
   Loopify neither rewrites an enum's match, a switch.  A call of a custom
   is its text, not a call.  A call with fewer arguments than its callee's
   parameters is a closure; one with more is an operand of the call it
   heads.  A saturated call continues in the partner's body where its
   result is the function's, unless the function returns unit, which it
   is generated returning nothing: it ends in the call's statement.
   [parameters g] is the number of parameters of [g], and [flow_body g]
   its body as generated, [None] where it is suspended whole. *)
let inlined_calls ~self ~effects ~parameters ~flow_body ~void ~inlines ~continued body =
  let effect_ = sequential effects in
  let found = ref [] in
  let continued_call use = List.exists (Occurrence.equal (Global_use.occurrence use)) continued in
  let rec go pos e =
    let operand = go Operand in
    match e with
    | MLapp (MLglob use, args) when Table.is_custom use.callee -> List.iter operand args
    | MLapp (MLglob use, args) when continued_call use ->
      List.iter operand args;
      Option.iter (go Returning) (flow_body use.callee)
    | MLapp (MLglob use, args) when inlines use.callee ->
      let n = List.length args and k = parameters use.callee in
      if n >= k then
        found :=
          { callee = use.callee;
            continues = n = k && (pos = Returning || pos = Returned) && not void;
            made_of = Global_use.occurrence use }
          :: !found;
      List.iter operand args
    | MLmagic (_, a) -> go pos a
    | MLcons (_, c, [a]) when identity c -> go pos a
    | MLapp (MLglob use, [a]) when identity use.callee && Table.to_inline use.callee -> go pos a
    | MLcons (Tglob (n, _, _), c, args)
      when (not (Table.is_custom c))
           && Translation_support.suspends_constructor ~self:(Some self) ~binder_type:(fun _ -> None) n
                args ->
      ()
    | MLletin (x, _, a, b, _) -> (
      match pos with
      | Operand | Returned -> ()
      | Returning | Binding ->
        if x != Dummy then go Binding a;
        go pos b )
    | MLcase (ty, s, branches) -> (
      let enum =
        match ty with
        | Tglob ((Names.GlobRef.IndRef _ as r), _, _) -> Table.is_enum_inductive r
        | _ -> false
      in
      match pos with
      | Operand | Returned -> ()
      | Binding when not (match_bound_in_place ty branches) -> ()
      | (Returning | Binding) when enum && not (Table.is_custom_match branches) -> ()
      | Returning | Binding ->
        operand s;
        Array.iter (fun (_, _, _, b) -> go pos b) branches )
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      match (pos, List.rev args) with
      | (Returning | Binding), MLlam (_, _, k) :: action :: rest ->
        List.iter operand (List.rev rest);
        operand action;
        go pos k
      | _ -> () )
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Return -> (
      match List.rev args with
      | value :: rest ->
        List.iter operand (List.rev rest);
        go (match pos with Returning | Returned -> Returned | Binding | Operand -> Operand) value
      | [] -> () )
    | MLapp (MLfix _, args) -> (
      match pos with Operand | Returned -> () | Returning | Binding -> List.iter operand args )
    | MLfix _ | MLlam _ -> ()
    | MLapp (f, args) ->
      operand f;
      List.iter operand args
    | MLcons (_, _, args) | MLtuple args -> List.iter operand args
    | MLparray (a, d) ->
      Array.iter operand a;
      operand d
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLfloat _ | MLstring _ -> ()
  in
  go Returning body;
  List.rev !found

(* The partners of [self] in its group [members] that Loopify inlines into
   it, in order, with the calls of each it inlines ({!inlined_calls}): the
   partner of the first call met that is of a partner not yet inlined,
   whose calls are all inlined at once, until none is met.  The calls that
   continue in a partner's body leave its calls in the body that later
   partners' are met in.  Each partner is inlined once: its calls in its own
   body stay calls. *)
let inlinings_of ~effects ~defs ~members self fd =
  let parameters g =
    match Ref.User.Map.find_opt g defs with
    | Some fd -> List.length (Ml_type_util.ml_domains (Mlutil.type_simpl fd.fd_type))
    | None -> 0
  in
  let flow_body g =
    Option.bind (Ref.User.Map.find_opt g defs) (fun fd ->
        let _, body = Core_elaborate.generated_scope fd.fd_type fd.fd_body in
        if Translation_support.suspends_whole g (Ml_type_util.ml_return_type fd.fd_type) body then None
        else Some body )
  in
  let void = Ml_type_util.ml_type_is_unit (Ml_type_util.ml_return_type fd.fd_type) in
  let calls ~inlines ~continued body =
    inlined_calls ~self ~effects ~parameters ~flow_body ~void ~inlines ~continued body
  in
  let is_partner g =
    (not (Common.globref_equal g self)) && List.exists (Common.globref_equal g) members
  in
  let rec plan inlined continued body =
    let pending g = is_partner g && not (List.exists (Common.globref_equal g) inlined) in
    match calls ~inlines:pending ~continued body with
    | [] -> []
    | {callee = partner; _} :: _ ->
      let found = calls ~inlines:(Common.globref_equal partner) ~continued body in
      let these continues = List.filter_map (fun c -> if c.continues = continues then Some c.made_of else None) found in
      let inlining = {partner; continued = these true; invoked = these false} in
      inlining :: plan (partner :: inlined) (continued @ inlining.continued) body
  in
  match flow_body self with Some body -> plan [] [] body | None -> []

(* The invocations the machine of [self] adopts, of those its [inlinings]
   leave: the first partner's that has some, and parameters, and whose body
   calls [self]. *)
let adopted_invocations_of ~defs self inlinings =
  let calls_self g =
    match Ref.User.Map.find_opt g defs with
    | None -> false
    | Some fd ->
      let exception Found in
      let rec walk = function
        | MLapp (MLglob use, _) when Common.globref_equal use.callee self -> raise Found
        | e -> Mlutil.ast_iter walk e
      in
      ( try walk (snd (Core_elaborate.generated_scope fd.fd_type fd.fd_body)); false with Found -> true )
  in
  let has_parameters g =
    match Ref.User.Map.find_opt g defs with
    | Some fd -> Ml_type_util.ml_domains (Mlutil.type_simpl fd.fd_type) <> []
    | None -> false
  in
  List.find_map
    (fun i -> if i.invoked <> [] && has_parameters i.partner && calls_self i.partner then Some i.invoked else None)
    inlinings

(* A group with partners is planned as one: Loopify inlines the partners
   into a member before reading it ({!inlinings_of}), so a loop of the
   member takes the calls of itself it then reads, in its body and in the
   partners' bodies inlined there, and only those: a partner's call it
   could not inline, or one of a third member in a partner's body run as
   an operand, stays a call of another function.  A function on no cycle
   calls no function it could recurse through. *)
let analyze groups struc =
  let effects = Core_effects.analyze struc in
  let defs = ref Ref.User.Map.empty in
  Modutil.struct_iter
    (fun d -> List.iter (fun fd -> defs := Ref.User.Map.add fd.fd_ref fd !defs) (Mlutil.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let defs = !defs in
  (* A function is generated taking every parameter its type declares, its
     body applied to those it does not bind ({!Core_elaborate.generated_scope}):
     its calls are read there, a call with fewer arguments than that being
     the closure the C++ makes of it. *)
  let parameters fd = List.length (Ml_type_util.ml_domains (Mlutil.type_simpl fd.fd_type)) in
  let inlinings =
    Ref.User.Map.mapi
      (fun r fd ->
        match Recursive_groups.group groups r with
        | Some members -> inlinings_of ~effects ~defs ~members r fd
        | None -> [] )
      defs
  in
  (* A member's own calls, its partners inlined as Loopify inlines them:
     what a loop of the member can take. *)
  let member_kind r fd =
    let callee ~depth:_ = function
      | MLglob use when Common.globref_equal use.callee r ->
        Option.map parameters (Ref.User.Map.find_opt use.callee defs)
      | _ -> None
    in
    let planned = Ref.User.Map.find r inlinings in
    let inlined (use : global_use) =
      let occurrence = Global_use.occurrence use in
      List.find_map
        (fun i ->
          let body () =
            Option.map
              (fun fd -> snd (Core_elaborate.generated_scope fd.fd_type fd.fd_body))
              (Ref.User.Map.find_opt i.partner defs)
          in
          if List.exists (Occurrence.equal occurrence) i.continued then
            Option.map (fun b -> Continues b) (body ())
          else if List.exists (Occurrence.equal occurrence) i.invoked then
            Option.map (fun b -> Invokes b) (body ())
          else None )
        planned
    in
    classify ~inlined ~effects ~callee (snd (Core_elaborate.generated_scope fd.fd_type fd.fd_body))
  in
  let kinds = Ref.User.Map.mapi member_kind defs in
  let plans =
    List.map
      (fun members ->
        let kind m = Option.default No_recursion (Ref.User.Map.find_opt m kinds) in
        {members; kind = List.fold_left (fun k m -> combine k (kind m)) No_recursion members} )
      (Recursive_groups.groups groups)
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
        let off_cycle_recurses () = Ref.User.Map.find r kinds <> No_recursion in
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
          let chains_of r =
            if Ref.User.Map.find_opt r kinds <> Some Nontail then None
            else Option.bind (index r) (modulo_cons_chains ~effects ~member ~bodies)
          in
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
        (* A call with fewer arguments than its callee's parameters is a
           closure the C++ makes, whose call runs where the closure does. *)
        let parameters g =
          match Ref.User.Map.find_opt g defs with
          | Some fd -> List.length (Ml_type_util.ml_domains (Mlutil.type_simpl fd.fd_type))
          | None -> 0
        in
        let rec targets = function
          | MLmagic (_, e) -> targets e
          | MLapp (MLglob use, args)
            when List.exists (Common.globref_equal use.callee) members
                 && List.length args >= parameters use.callee ->
            [{target = Function use.callee; occurrence = Global_use.occurrence use}]
          | _ -> []
        in
        let lex, body = Core_elaborate.generated_scope fd.fd_type fd.fd_body in
        resumes_of ~effects ~origin:r ~targets lex body )
      defs
  in
  let adoptable =
    Ref.User.Map.mapi
      (fun r fd ->
        let members = match Ref.User.Map.find_opt r by_member with Some g -> g.members | None -> [] in
        let names ~depth:_ = function
          | MLglob use -> List.exists (Common.globref_equal use.callee) members
          | _ -> false
        in
        let lex, body = Core_elaborate.generated_scope fd.fd_type fd.fd_body in
        flow_fixpoints ~names (Lexenv.depth lex) body )
      defs
  in
  let adopted_invocations =
    Ref.User.Map.fold
      (fun r is m ->
        match adopted_invocations_of ~defs r is with Some occs -> Ref.User.Map.add r occs m | None -> m )
      inlinings Ref.User.Map.empty
  in
  { groups = plans;
    by_member;
    defined;
    locals = local_groups ~effects defs;
    modulo_cons;
    suspended;
    resumes;
    adoptable;
    inlinings;
    adopted_invocations;
    kinds;
    let_lambdas =
      Ref.User.Map.fold
        (fun _ fd found ->
          let found = ref found in
          let rec walk e =
            ( match e with MLletin (_, _, MLlam _, _, occ) -> found := occ :: !found | _ -> () );
            Mlutil.ast_iter walk e
          in
          walk fd.fd_body;
          !found )
        defs [] }

let same_cell c c' = Common.globref_equal c.constructor c'.constructor && c.hole = c'.hole

let same_chains =
  List.equal (fun c c' ->
      List.equal same_cell c.around c'.around && same_cell c.innermost c'.innermost )

let same_target t t' =
  match (t, t') with
  | Function g, Function g' -> Common.globref_equal g g'
  | Member (o, m), Member (o', m') -> Occurrence.equal o o' && Int.equal m m'
  | Entering o, Entering o' -> Occurrence.equal o o'
  | (Function _ | Member _ | Entering _), _ -> false

let same_call c c' = same_target c.target c'.target && Occurrence.equal c.occurrence c'.occurrence

let equal a b =
  List.equal
    (fun g g' -> List.equal Common.globref_equal g.members g'.members && g.kind = g'.kind)
    a.groups b.groups
  && Ref.User.Set.equal a.defined b.defined
  && List.equal
       (fun (l : local_group) (l' : local_group) ->
         Occurrence.equal l.occurrence l'.occurrence
         && l.local_kind = l'.local_kind
         && List.equal (Option.equal same_chains) l.chains l'.chains
         && l.suspends = l'.suspends
         && List.equal (List.equal Occurrence.equal) l.adoptable l'.adoptable
         && List.equal (List.equal Occurrence.equal) l.calls l'.calls )
       a.locals b.locals
  && Ref.User.Map.equal same_chains a.modulo_cons b.modulo_cons
  && Ref.User.Set.equal a.suspended b.suspended
  && Ref.User.Map.equal
       (List.equal (fun r r' ->
            Core_binder.equal r.binder r'.binder
            && Core_binder.same_site r.binder r'.binder
            && List.equal Core_binder.equal r.live r'.live
            && List.equal same_call r.after r'.after ) )
       a.resumes b.resumes
  && Ref.User.Map.equal (List.equal Occurrence.equal) a.adoptable b.adoptable
  && Ref.User.Map.equal
       (List.equal (fun i i' ->
            Common.globref_equal i.partner i'.partner
            && List.equal Occurrence.equal i.continued i'.continued
            && List.equal Occurrence.equal i.invoked i'.invoked ) )
       a.inlinings b.inlinings
  && Ref.User.Map.equal (List.equal Occurrence.equal) a.adopted_invocations b.adopted_invocations
  && Ref.User.Map.equal ( = ) a.kinds b.kinds
  && List.equal Occurrence.equal a.let_lambdas b.let_lambdas

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

(* A member's kind is its own calls', its partners inlined; a partner is
   inlined into a member, its suspensions with it. *)
let strategy ~pointer_fields r =
  if Ref.User.Set.mem r !installed.defined then
    let kind = Option.default No_recursion (Ref.User.Map.find_opt r !installed.kinds) in
    let members = match group_of r with Some g -> g.members | None -> [r] in
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
    (fun found (l : local_group) ->
      if Occurrence.equal l.occurrence occurrence then
        match List.nth_opt l.chains member with
        | Some chains ->
          let this = strategy_of ~pointer_fields ~suspends:l.suspends l.local_kind chains in
          Some (match found with Some f -> both f this | None -> this)
        | None -> found
      else found )
    None !installed.locals

let adoptable r =
  Option.default [] (Ref.User.Map.find_opt r !installed.adoptable)

(* Copies of a fixpoint share its occurrence, and plan alike. *)
let adoptable_at (occurrence, member) =
  List.find_map
    (fun (l : local_group) ->
      if Occurrence.equal l.occurrence occurrence then List.nth_opt l.adoptable member else None )
    !installed.locals
  |> Option.default []

(* Copies of a fixpoint share its occurrence, and so do their calls. *)
let member_calls (occurrence, member) =
  List.concat_map
    (fun (l : local_group) ->
      if Occurrence.equal l.occurrence occurrence then Option.default [] (List.nth_opt l.calls member)
      else [] )
    !installed.locals

let resumes_binding (b : Core_binder.t) =
  match Ref.User.Map.find_opt b.origin !installed.resumes with
  | Some rs -> List.filter (fun r -> Core_binder.equal r.binder b && Core_binder.same_site r.binder b) rs
  | None -> []

let inlinings r = Option.default [] (Ref.User.Map.find_opt r !installed.inlinings)

let adopted_invocations r = Ref.User.Map.find_opt r !installed.adopted_invocations

(* A lambda a let binds does not call itself. *)
let strategy_of_let occurrence =
  if List.exists (Occurrence.equal occurrence) !installed.let_lambdas then Some No_loop else None
