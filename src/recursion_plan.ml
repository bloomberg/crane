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

(* The plan of one local fixpoint, the counterpart of a definition's
   entries in [t]: per member lists are in the fixpoint's member order. *)
type local_group = {
  occurrence : Occurrence.t;  (* the fixpoint's *)
  local_kind : kind;  (* the group's, as the member that recurses most *)
  chains : chain list option list;
      (* per member, its chains, if it recurses through no other call that
         is not a tail call *)
  suspends : bool;  (* some member's body suspends ({!suspends_within}) *)
  adoptable : Occurrence.t list list;  (* per member, {!flow_fixpoints} calling the group *)
  calls : Occurrence.t list list;
      (* per member, the reads heading its calls in the group's bodies *)
  named : bool list;  (* per member, whether the group's bodies read it other than at a call's head *)
  entered : Occurrence.t list;
      (* the calls of the member the fixpoint stands for made where it is
         bound: the fixpoint applied, or the reads of the let binding it *)
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
   reads, which a frame keeps across the call, the calls it resumes after,
   those of the live binders the calls' arguments read, and the binders in
   scope whose value makes no call, with those it reads. *)
type resume = {
  binder : Core_binder.t;
  live : Core_binder.t list;
  after : call list;
  passes : passing list;
  read_by_call : Core_binder.t list;
  recomputable : recomputable list;
}

(* A live binder passed on, as it is, for a parameter of a recursive call. *)
and passing = {
  passed : Core_binder.t;
  into : Core_binder.t;
  call : call;
}

(* A binder whose value makes no call, and the binders it reads. *)
and recomputable = {
  recomputed : Core_binder.t;
  from : Core_binder.t list;
}

type t = {
  groups : group list;  (* one per recursive group *)
  by_member : group Ref.User.Map.t;  (* each member's group *)
  defined : Ref.User.Set.t;  (* every function the program defines *)
  locals : local_group list;  (* one per local fixpoint, copies included *)
  modulo_cons : chain list Ref.User.Map.t;
      (* per definition that recurses by some call that is not a tail call,
         its chains, if every such call is the one call of a chain *)
  suspended : Ref.User.Set.t;  (* the definitions whose body suspends *)
  resumes : resume list Ref.User.Map.t;  (* per definition, its resume points *)
  adoptable : Occurrence.t list Ref.User.Map.t;  (* per definition, {!flow_fixpoints} calling its group *)
  kinds : kind Ref.User.Map.t;  (* per definition, its own calls *)
  calls : Occurrence.t list Ref.User.Map.t;  (* per member, the uses heading its calls in its group's bodies *)
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
    kinds = Ref.User.Map.empty;
    calls = Ref.User.Map.empty;
    let_lambdas = [] }

(* The number of lambdas heading a term, plus [n], and the body under them. *)
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
   sequentially. *)
let classify ~effects ~callee body =
  let tail_call = ref false and nontail_call = ref false in
  let effect_ = sequential effects in
  let rec walk ~depth ~tail e =
    let walk_under n ~tail e = walk ~depth:(depth + n) ~tail e in
    let walk ~tail e = walk ~depth ~tail e in
    match e with
    | f when callee ~depth f = Some 0 -> if tail then tail_call := true else nontail_call := true
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
    | MLcase (_, s, branches, _) ->
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
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLnumeral _ | MLfloat _ | MLstring _ ->
      ()
  and continuation ~depth ~tail = function
    | MLlam _ as k ->
      let n, b = split_params 0 k in
      walk ~depth:(depth + n) ~tail b
    | k -> walk ~depth ~tail:false k
  in
  walk ~depth:0 ~tail:true body;
  if !nontail_call then Nontail else if !tail_call then Tail else No_recursion

(* The kind of a group of two kinds: the one that recurses most. *)
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
   member [within], under [depth] binders inside its parameters.  A tail
   call to a partner is read as continuing in the partner's body; any other
   call to a partner is out of reach.  A partner already read so is called
   as any function is. *)
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
      | MLcase (_, s, branches, _) ->
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
    | MLcase (_, s, branches, _) ->
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
  | MLcase (_, s, branches, _) ->
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

(* The levels of the binders outside [e] that [e] reads as values, [e]
   standing under [depth] binders: one at a level of [heads] read only to
   call it is not. *)
let value_levels ~heads ~depth e =
  let found = ref [] in
  let rec go d = function
    | MLrel (i, _) -> if i > d then found := (depth + d - i) :: !found
    | MLapp (MLrel (i, _), args) when i > d && List.mem (depth + d - i) heads -> List.iter (go d) args
    | MLlam (_, _, b) -> go (d + 1) b
    | MLletin (_, _, a, b, _) ->
      go d a;
      go (d + 1) b
    | MLcase (_, s, branches, _) ->
      go d s;
      Array.iter (fun (ids, _, _, b) -> go (d + List.length ids) b) branches
    | MLfix (_, ids, funs, _, _) -> Array.iter (go (d + Array.length ids)) funs
    | e -> Mlutil.ast_iter (go d) e
  in
  go 0 e;
  List.sort_uniq Int.compare !found

let rec strip = function MLmagic (_, e) -> strip e | e -> e

let in_place from into =
  match (Mlutil.type_simpl from, Mlutil.type_simpl into) with
  | Tglob ((Names.GlobRef.IndRef (kn, _) as r), args, _), Tglob (r', args', _)
    when Names.GlobRef.UserOrd.equal r r' -> (
    match Table.get_ind_num_param_vars_opt kn with
    | Some n when List.length args >= n && List.length args' >= n ->
      List.for_all2 Mlutil.eq_ml_type (CList.firstn n args) (CList.firstn n args')
    | Some _ | None -> false )
  | _ -> false

(* [e] through the coercions keeping its representation: the value a
   parameter is passed where the argument is [e]. *)
let rec as_passed = function
  | MLmagic (Mcoerce (from, into), e) when in_place from into -> as_passed e
  | e -> e

(* The arguments a call is applied to, through coercions. *)
let rec arguments = function MLmagic (_, e) -> arguments e | MLapp (_, args) -> args | _ -> []

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
   call of a member of that fixpoint is one too, as is, in the body of a
   let binding a partner's copy the machine enters ([entered]), a
   call of the copy, which is no value kept.  A call under a lambda is
   made where the closure runs, not here, but a local fixpoint in the
   lambda's body is lowered on its own, and resumes after its own calls.

   What a point keeps is what follows reads as a value: not a dictionary
   the declaration takes, which C++ takes as a template argument, nor a
   member of a local fixpoint whose calls the point is among -- [heads],
   those whose bodies it is in -- called, which enters the machine again. *)
let resumes_of ~effects ~entered ~origin ~targets lex body =
  let effect_ = sequential effects in
  let found = ref [] in
  let binder level = Core_binder.make ~origin ~level () in
  let dictionary level =
    match Lexenv.binder lex (Lexenv.depth lex - level) with
    | Some {eb_role = Dictionary; _} -> true
    | Some {eb_role = Value; _} | None -> false
  in
  let dedup_passings ps =
    let same p p' =
      Core_binder.equal p.passed p'.passed && Core_binder.equal p.into p'.into
      && Occurrence.equal p.call.occurrence p'.call.occurrence
    in
    List.fold_left (fun acc p -> if List.exists (same p) acc then acc else acc @ [p]) [] ps
  in
  (* The parameter the [i]th argument of the recursive call [c] is passed
     for: the [i]th of the function's, or of the fixpoint's member, its
     members bound from level [first] of [fixpoints] on. *)
  let into ~fixpoints (c : call) i =
    match c.target with
    | Function g -> Some (Core_binder.make ~origin:g ~level:i ())
    | Member (o, _) ->
      Option.map
        (fun (first, n) -> binder (first + n + i))
        (List.find_map (fun (o', fn) -> if Occurrence.equal o o' then Some fn else None) fixpoints)
    | Entering _ -> None
  in
  (* The live binders [rest], standing under [depth] binders, passes on to
     a recursive call [targets] names that enters the machine: one whose
     value is what a let or a bind binds, or what [rest] returns.  A call
     whose value goes into some other term stays a call. *)
  let passings ~fixpoints ~targets ~live depth rest =
    let found = ref [] in
    let rec go ~enters d e =
      ( match targets ~depth:(depth + d) e with
      | [c] when enters ->
        List.iteri
          (fun i a ->
            match as_passed a with
            | MLrel (j, _) when j > d && List.mem (depth + d - j) live ->
              Option.iter
                (fun p -> found := {passed = binder (depth + d - j); into = p; call = c} :: !found)
                (into ~fixpoints c i)
            | _ -> () )
          (arguments e)
      | _ -> () );
      match e with
      | MLlam _ | MLfix _ -> ()
      | MLletin (_, _, a, b, _) ->
        go ~enters:true d a;
        go ~enters (d + 1) b
      | MLcase (_, s, branches, _) ->
        go ~enters:false d s;
        Array.iter (fun (ids, _, _, b) -> go ~enters (d + List.length ids) b) branches
      | MLmagic (_, e) -> go ~enters d e
      | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
        match List.rev args with
        | MLlam (_, _, k) :: action :: others ->
          go ~enters:true d action;
          List.iter (go ~enters:false d) others;
          go ~enters (d + 1) k
        | _ -> List.iter (go ~enters:false d) args )
      | e -> Mlutil.ast_iter (go ~enters:false d) e
    in
    go ~enters:true 0 rest;
    List.rev !found
  in
  (* A local the frames of consecutive points keep is kept alike in all of
     them, each handler passing it to the next frame as it holds it: what
     follows a point passes it on as what follows the outermost of them,
     [enclosing], does too. *)
  let resume ~heads ~fixpoints ~targets ~enclosing ~site ~after ~arguments_read ~recipes depth rest =
    let live =
      List.filter (fun l -> l <> depth && not (dictionary l)) (value_levels ~heads ~depth:(depth + 1) rest)
    in
    let live_binders = List.map binder live in
    let inherited =
      List.concat_map
        (fun r -> List.filter (fun q -> List.exists (Core_binder.equal q.passed) live_binders) r.passes)
        enclosing
    in
    let r =
      { binder = Core_binder.make ~origin ~level:depth ~site:(Binding site) ();
        live = live_binders;
        after;
        passes = dedup_passings (inherited @ passings ~fixpoints ~targets ~live (depth + 1) rest);
        read_by_call = List.map binder (List.filter (fun l -> List.mem l arguments_read) live);
        recomputable =
          List.filter_map
            (fun (l, reads) ->
              if dictionary l then None
              else Some {recomputed = binder l; from = List.map binder (List.filter (fun r -> not (dictionary r)) reads)} )
            recipes }
    in
    found := r :: !found;
    r
  in
  let rec walk ~targets ~heads ~fixpoints ~enclosing ~closures ~fields ~captures depth e =
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
      | MLcase (_, s, branches, _) ->
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
        | MLcase (ty, _, branches, _) when match_bound_in_place ty branches ->
          List.concat_map
            (fun (ids, _, _, b) -> ending (depth + List.length ids) b)
            (Array.to_list branches)
        | MLletin (_, _, _, b, _) -> ending (depth + 1) b
        | MLmagic (_, b) -> ending depth b
        | _ -> [] )
    in
    (* The levels [levels], with those the closures among them read: a
       closure a let binds reads what it captures when it is called, which
       may be where the call it is passed to is made, and a reference it
       captures by then still names the local. *)
    let rec through_closures seen levels =
      List.concat_map
        (fun l ->
          if List.mem l seen then []
          else
            l
            ::
            match List.assoc_opt l closures with
            | Some a -> through_closures (l :: seen) (value_levels ~heads ~depth:l a)
            | None -> [] )
        levels
    in
    (* The levels the calls [calls], applied to [args], read as values: what
       their arguments read, and what a local fixpoint called captures --
       taken as arguments where a machine adopts it. *)
    let calls_read depth calls args =
      let captured (c : call) =
        match c.target with
        | Member (o, _) | Entering o ->
          Option.default [] (List.find_map (fun (o', l) -> if Occurrence.equal o o' then Some l else None) captures)
        | Function _ -> []
      in
      through_closures [] (List.concat_map (value_levels ~heads ~depth) args @ List.concat_map captured calls)
    in
    (* The levels the calls a right-hand side ends in read as values, along
       the branches {!ending} follows: what is still read once a frame is
       saved, where the call it is saved for is made. *)
    let rec arguments_read depth e =
      match targets ~depth e with
      | _ :: _ as calls -> calls_read depth calls (arguments e)
      | [] -> (
        match e with
        | MLapp ((MLfix _ as fix), args) when reaches depth fix ->
          through_closures [] (value_levels ~heads ~depth fix) @ calls_read depth [] args
        | MLcase (ty, _, branches, _) when match_bound_in_place ty branches ->
          List.concat_map
            (fun (ids, _, _, b) -> arguments_read (depth + List.length ids) b)
            (Array.to_list branches)
        | MLletin (_, _, _, b, _) -> arguments_read (depth + 1) b
        | MLmagic (_, b) -> arguments_read depth b
        | _ -> [] )
    in
    let go = walk ~targets ~heads ~fixpoints ~enclosing ~closures ~fields ~captures in
    (* The binders in scope whose value makes no call, outermost first,
       with the levels it reads: a closure a let binds, which reads what it
       captures, and a pattern variable of a record's one branch matching a
       variable, a field of that variable. *)
    let recipes =
      List.sort
        (fun (l, _) (l', _) -> Int.compare l l')
        (List.map (fun (l, a) -> (l, value_levels ~heads:[] ~depth:l a)) closures
        @ List.map (fun (l, s) -> (l, [s])) fields)
    in
    let resuming ~site ~after ~arguments_read depth rest =
      match after with
      | [] -> enclosing
      | after -> resume ~heads ~fixpoints ~targets ~enclosing ~site ~after ~arguments_read ~recipes depth rest :: enclosing
    in
    match e with
    | MLletin (_, _, a, b, site) ->
      let enclosing = resuming ~site ~after:(ending depth a) ~arguments_read:(arguments_read depth a) depth b in
      go depth a;
      let rec closure = function MLlam _ | MLfix _ -> true | MLmagic (_, e) -> closure e | _ -> false in
      let closures = if closure a then (depth, a) :: closures else closures in
      (* The let binding a partner's copy the machine enters: its calls in
         the body are the copy's, a member of the fixpoint at that level. *)
      let targets, heads, fixpoints, captures =
        match a with
        | MLfix (_, [|_|], [|_|], false, occ) when entered occ ->
          let level = depth in
          let rec entering ~depth:d = function
            | MLmagic (_, e) -> entering ~depth:d e
            | MLapp (MLrel (k, read), _) when d - k = level -> [{target = Member (occ, 0); occurrence = read}]
            | e -> targets ~depth:d e
          in
          (entering, level :: heads, (occ, (depth, 1)) :: fixpoints, (occ, value_levels ~heads ~depth a) :: captures)
        | _ -> (targets, heads, fixpoints, captures)
      in
      walk ~targets ~heads ~fixpoints ~enclosing ~closures ~fields ~captures (depth + 1) b
    | MLapp (MLglob use, args) when effect_ use = Some Core_effects.Bind -> (
      match List.rev args with
      | MLlam (_, _, k) :: action :: rest ->
        let after = targets ~depth action in
        let arguments_read = if after = [] then [] else calls_read depth after (arguments action) in
        let enclosing = resuming ~site:(Global_use.occurrence use) ~after ~arguments_read depth k in
        List.iter (go depth) (action :: rest);
        walk ~targets ~heads ~fixpoints ~enclosing ~closures ~fields ~captures (depth + 1) k
      | _ -> List.iter (go depth) args )
    | MLcase (ty, s, [|(ids, _, _, b)|], _) when Table.record_fields_of_type ty <> [] -> (
      go depth s;
      match strip s with
      | MLrel (i, _) ->
        let n = List.length ids in
        let fields = List.init n (fun k -> (depth + k, depth - i)) @ fields in
        walk ~targets ~heads ~fixpoints ~enclosing ~closures ~fields ~captures (depth + n) b
      | _ -> go (depth + List.length ids) b )
    | MLcase (_, s, branches, _) ->
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
      let heads = heads @ List.init n (fun m -> first + m) in
      let fixpoints = (occ, (first, n)) :: fixpoints in
      let captures = (occ, value_levels ~heads ~depth e) :: captures in
      Array.iter
        (fun f ->
          let arity, b = split_params 0 f in
          walk ~targets ~heads ~fixpoints ~enclosing:[] ~closures ~fields ~captures (depth + n + arity) b )
        funs
    | MLlam (_, _, b) ->
      walk ~targets:(fun ~depth:_ _ -> []) ~heads:[] ~fixpoints ~enclosing:[] ~closures ~fields ~captures (depth + 1) b
    | e -> Mlutil.ast_iter (go depth) e
  in
  walk ~targets:(fun ~depth:_ e -> targets e) ~heads:[] ~fixpoints:[] ~enclosing:[] ~closures:[] ~fields:[] ~captures:[]
    (Lexenv.depth lex) body;
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
    | MLcase (_, s, branches, _) ->
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
    | MLcase (_, s, branches, _) ->
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
  | MLcase (_, s, branches, _) ->
    iter_under f depth s;
    Array.iter (fun (ids, _, _, b) -> iter_under f (depth + List.length ids) b) branches
  | MLfix (_, ids, funs, _, _) -> Array.iter (iter_under f (depth + Array.length ids)) funs
  | e -> Mlutil.ast_iter (iter_under f depth) e

(* The calls of each local fixpoint in [body] made where it is bound, under
   its occurrence: the fixpoint applied there, by its occurrence, or the
   reads of the let binding it. *)
let bound_calls body =
  let found = ref [] in
  let rec walk e =
    ( match e with
    | MLletin (_, _, MLfix (_, _, _, _, occurrence), b, _) ->
      let reads = ref [] in
      iter_under (fun depth -> function MLrel (k, read) when k = depth + 1 -> reads := read :: !reads | _ -> ()) 0 b;
      found := (occurrence, List.rev !reads) :: !found
    | MLapp (MLfix (_, _, _, _, occurrence), _) -> found := (occurrence, [occurrence]) :: !found
    | _ -> () );
    Mlutil.ast_iter walk e
  in
  walk body;
  !found

(* The plan of every local fixpoint in [defs], one per fixpoint, under its
   occurrence.  Inside a member's body, before its parameters,
   the member [k] of [n] is the variable [n - k]. *)
let local_groups ~effects defs =
  let plans = ref [] in
  let plan ~bound origin lex ids funs occurrence =
    let n = Array.length ids in
    let arities = Array.map (fun f -> fst (split_params 0 f)) funs in
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
    let calls, reads =
      let calls = Array.make n [] and reads = Array.make n [] in
      Array.iteri
        (fun j f ->
          iter_under
            (fun depth e ->
              match (member ~within:j ~depth e, e) with
              | Some k, MLrel (_, read) -> reads.(k) <- read :: reads.(k)
              | _ -> (
                match e with
                | MLapp (head, _) -> (
                  match (member ~within:j ~depth head, strip head) with
                  | Some k, MLrel (_, read) -> calls.(k) <- read :: calls.(k)
                  | _ -> () )
                | _ -> () ) )
            0
            (snd (split_params 0 f)) )
        funs;
      (Array.to_list calls, Array.to_list reads)
    in
    let named =
      List.map2 (fun calls reads -> List.exists (fun r -> not (List.exists (Occurrence.equal r) calls)) reads) calls reads
    in
    plans :=
      { occurrence;
        local_kind = kind;
        chains;
        suspends;
        adoptable;
        calls;
        named;
        entered = List.concat_map (fun (o, calls) -> if Occurrence.equal o occurrence then calls else []) bound }
      :: !plans
  in
  Ref.User.Map.iter
    (fun r fd ->
      let lex, body = Core_elaborate.declaration_scope fd.fd_type fd.fd_body in
      let bound = bound_calls body in
      iter_scoped
        (fun lex -> function MLfix (_, ids, funs, _, occ) -> plan ~bound r lex ids funs occ | _ -> ())
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

(* The partners' calls whose uses [inlines] holds that run in [body] as
   translation generates it, the body of the function [self], in the order
   they are met.  A call runs there unless it stands in a lambda: a
   closure's body, a local fixpoint's, a suspended coinductive constructor's
   arguments or a body suspended whole, and a match, let, fixpoint or bind
   that is an operand, which translation runs in a lambda invoked in place,
   as it does a match bound by a let that is no custom or record match.
   Nor does a call in an enum's match, generated as a switch, which Loopify
   does not rewrite.  A call of a custom
   is its text, not a call.  A call with fewer arguments than its callee's
   parameters is a closure; one with more is an operand of the call it
   heads.  A saturated call continues in the partner's body where its
   result is the function's -- in one returning unit, the call's statement
   and the return after it.  [parameters g] is the number of parameters of
   [g]. *)
let inlined_calls ~self ~effects ~parameters ~inlines body =
  let effect_ = sequential effects in
  let found = ref [] in
  let rec go pos e =
    let operand = go Operand in
    match e with
    | MLapp (MLglob use, args) when Table.is_custom use.callee -> List.iter operand args
    | MLapp (MLglob use, args) when inlines use ->
      let n = List.length args and k = parameters use.callee in
      if n >= k then
        found :=
          { callee = use.callee;
            continues = n = k && (pos = Returning || pos = Returned);
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
    | MLcase (ty, s, branches, _) -> (
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
    | MLrel _ | MLglob _ | MLexn _ | MLdummy _ | MLaxiom _ | MLuint _ | MLnumeral _ | MLfloat _ | MLstring _ -> ()
  in
  go Returning body;
  List.rev !found

(* The body of the function [r], defined as [fd], as it is generated: [None]
   where it is suspended whole. *)
let flow_of r fd =
  let _, body = Core_elaborate.declaration_scope fd.fd_type fd.fd_body in
  if Translation_support.suspends_whole r (Ml_type_util.ml_return_type fd.fd_type) body then None else Some body

(* The number of parameters the definition [fd] is generated taking: every
   one its type declares. *)
let fd_parameters fd = List.length (Ml_type_util.ml_domains (Mlutil.type_simpl fd.fd_type))

(* The number of parameters of [g], among the definitions [defs]. *)
let parameters defs g =
  match Ref.User.Map.find_opt g defs with
  | Some fd -> fd_parameters fd
  | None -> 0

(* The partner of [self] spliced next into [body], its body as generated,
   with the calls of it spliced ({!inlined_calls}): the partner of the first
   such call met of a function [pending] holds, whose calls are all spliced
   at once.  A call [opaque] holds is in a partner's body run in place of a
   call, where nothing is spliced. *)
let next_inlining ~opaque ~effects ~defs ~pending self body =
  let calls ~inlines =
    let inlines (use : global_use) =
      inlines use.callee && not (List.exists (Occurrence.equal (Global_use.occurrence use)) opaque)
    in
    inlined_calls ~self ~effects ~parameters:(parameters defs) ~inlines body
  in
  match calls ~inlines:pending with
  | [] -> None
  | {callee = partner; _} :: _ ->
    let found = calls ~inlines:(Common.globref_equal partner) in
    let these continues = List.filter_map (fun c -> if c.continues = continues then Some c.made_of else None) found in
    Some {partner; continued = these true; invoked = these false}

(* Why the partners of [r] are not spliced. *)
let unspliced why r =
  Probe.hit "SPLICE_declined" (fun () -> why ^ " " ^ Table.kername_of_global r);
  None

(* Whether the use [use] solves one of its callee's variables to a type, or
   is written at a type other than the variable in its place: the callee's
   body is then another function there.  A use within its callee's
   recursive group is solved at the group's own variables, whatever it is
   written at -- [g bool] in [g]'s partner. *)
let solves_variables use =
  let solved =
    Option.cata
      (Scheme.Instantiation.exists (fun _ (s : ml_type Scheme.slot) ->
           match s.solution with Scheme.Type _ -> true | Scheme.Identity -> false ) )
      false (Global_use.instantiation use)
  in
  let written_elsewhere (v, t) =
    match Mlutil.type_simpl t with Tvar (_, i) -> i <> Scheme.Var.ordinal v | _ -> true
  in
  solved || List.exists written_elsewhere (Global_use.written_evidence use)

(* The occurrences of the global uses in [e]. *)
let uses_in e =
  let found = ref [] in
  let rec walk = function
    | MLglob use -> found := Global_use.occurrence use :: !found
    | e -> Mlutil.ast_iter walk e
  in
  walk e;
  !found

(* [body] with each call of the function defined as [def] made at [sites]
   replaced by [def]'s body, its parameters bound to the call's arguments
   ({!Core_copy.call}), and the uses in the bodies so copied; [Error why]
   unless every site is such a call, with an argument for each parameter,
   of a use that solves none of its callee's variables, whose body then
   needs no instantiation. *)
let splice_calls def sites body =
  let left = ref sites and copied = ref [] in
  let at use = List.exists (Occurrence.equal (Global_use.occurrence use)) !left in
  let exception Unspliced of string in
  let rec go e =
    match e with
    | MLapp (MLglob use, args) when at use -> (
      if solves_variables use then raise_notrace (Unspliced "instantiated");
      match Core_copy.call ~ty:def.fd_type use def.fd_body args with
      | None -> raise_notrace (Unspliced "arguments")
      | Some spliced ->
        left := List.filter (fun o -> not (Occurrence.equal o (Global_use.occurrence use))) !left;
        let passed = List.concat_map uses_in args in
        copied := List.filter (fun o -> not (List.exists (Occurrence.equal o) passed)) (uses_in spliced) @ !copied;
        spliced )
    | _ -> Mlutil.ast_map go e
  in
  match go body with
  | body -> if !left = [] then Ok (body, !copied) else Error "unreached"
  | exception Unspliced why -> Error why

(* The effect operations of [fd]'s body alone, generated in its mode. *)
let definition_effects fd =
  Core_effects.analyze [(Names.ModPath.MPfile Names.DirPath.empty, [(Names.Label.make "spliced", SEdecl (Dfix [fd]))])]

(* Whether functions of types [a] and [b] yield one type, once every
   abbreviation is unfolded, whatever [Type Expand] says the C++ spells, a
   variable of the definition's scheme read alike whether it is written as
   the scheme's or, under a binder inside it, as rigid. *)
let yields_alike a b =
  let rec unfold = function
    | Tmeta {contents = Some t} -> unfold t
    | Tglob ((Names.GlobRef.ConstRef kn as r), args, a) -> (
      match Table.lookup_typedef_unchecked kn with
      | Some t -> unfold (Mlutil.type_subst_list args t)
      | None -> Tglob (r, List.map unfold args, a) )
    | Tglob (r, args, a) -> Tglob (r, List.map unfold args, a)
    | Tapp (i, args) -> Tapp (i, List.map unfold args)
    | Tarr (a, b) -> Tarr (unfold a, unfold b)
    | t -> t
  in
  let returns ty = Mlutil.rigidify (unfold (Ml_type_util.ml_return_type (Mlutil.type_simpl ty))) in
  Mlutil.eq_ml_type (returns a) (returns b)

(* The calls of [g] the partner [def] makes where its body runs in place of
   a call of it ({!inlined_calls}), and the number of its uses of [g] there
   in all. *)
let flow_calls ~defs def g =
  match flow_of def.fd_ref def with
  | None -> ([], 0)
  | Some body ->
    let of_g (use : global_use) = Common.globref_equal use.callee g in
    let uses = ref 0 in
    let rec count = function MLglob use when of_g use -> incr uses | e -> Mlutil.ast_iter count e in
    count body;
    ( inlined_calls ~self:def.fd_ref ~effects:(definition_effects def) ~parameters:(parameters defs) ~inlines:of_g
        body,
      !uses )

(* The calls of [self] the partner [def] makes where its body runs in place
   of a call of it. *)
let calls_back ~defs ~self def = fst (flow_calls ~defs def self)

(* Whether each use the partner [def] makes of itself is a call where its
   body runs: the copy a machine enters is no value, so a use in a closure,
   a partial application or anything run in a lambda would have nothing to
   call. *)
let calls_itself_in_flow ~defs def =
  let calls, uses = flow_calls ~defs def def.fd_ref in
  List.length calls = uses

(* [body], the body of a function, with each call of its partner defined as
   [def] made at [sites] replaced by a call of a copy of the partner bound in
   front of it, and the occurrence of the copy: a local fixpoint whose calls
   of the partner are its own, so that the machine entering it where the
   calls were runs every turn of the partner as one of its own.  [Error why]
   unless every site is such a call, with an argument for each of the
   partner's parameters, of a use that solves none of its variables, as is
   every call of the partner its body makes. *)
let adopt_calls def sites body =
  let partner = def.fd_ref in
  let arity = List.length (Ml_type_util.ml_domains (Mlutil.type_simpl def.fd_type)) in
  let left = ref sites in
  let at use = List.exists (Occurrence.equal (Global_use.occurrence use)) !left in
  let exception Unspliced of string in
  let instance use = if solves_variables use then raise_notrace (Unspliced "instantiated") in
  let rec own depth = function
    | MLglob use when Names.GlobRef.UserOrd.equal use.callee partner ->
      instance use;
      MLrel (depth + 1, Occurrence.fresh ())
    | e -> Mlutil.ast_map_lift own depth e
  in
  let rec reroute depth e =
    match e with
    | MLapp (MLglob use, args) when at use ->
      instance use;
      if List.length args <> arity then raise_notrace (Unspliced "arguments");
      left := List.filter (fun o -> not (Occurrence.equal o (Global_use.occurrence use))) !left;
      MLapp (MLrel (depth + 1, Occurrence.fresh ()), List.map (reroute depth) args)
    | _ -> Mlutil.ast_map_lift reroute depth e
  in
  let params, inner = Mlutil.collect_lams body in
  match (own 0 (Core_copy.copy def.fd_body), reroute 0 (Mlutil.ast_lift 1 inner)) with
  | _ when arity = 0 -> Error "arguments"
  | _ when !left <> [] -> Error "unreached"
  | copy, inner ->
    let name = Names.Id.of_string (Names.Id.to_string (Table.safe_basename_of_global partner) ^ "_entry") in
    let entered = Occurrence.fresh () in
    let fixpoint = MLfix (0, [|(name, def.fd_type)|], [|copy|], false, entered) in
    Ok (Mlutil.named_lams params (MLletin (Id name, def.fd_type, fixpoint, inner, Occurrence.fresh ())), entered)
  | exception Unspliced why -> Error why

(* Whether the function defined as [fd] calls itself once its partners are
   spliced into it: only a function that does is lowered as a loop. *)
let recurses fd =
  let arity = List.length (Ml_type_util.ml_domains (Mlutil.type_simpl fd.fd_type)) in
  let callee ~depth:_ = function
    | MLglob use when Names.GlobRef.UserOrd.equal use.callee fd.fd_ref -> Some arity
    | _ -> None
  in
  let _, body = Core_elaborate.declaration_scope fd.fd_type fd.fd_body in
  classify ~effects:(definition_effects fd) ~callee body <> No_recursion

(* The partners of [fd], a function of the group [members], in the order
   they are spliced into it ({!next_inlining}), its body with them spliced
   into it, and the occurrence of the partner it enters, if any.  A
   partner's tail calls continue in a copy of its body.  Its other calls,
   where [inlines] says the partners of [fd] are inlined into it at all, are
   entered as a copy its machine enters ({!adopt_calls}) -- where none is
   entered yet, the partner yields what [fd] does and its body, run in
   place, calls [fd] back -- or else run a copy of its body in their place,
   as a call would.  Once no partner is left to splice, a partner whose
   copies brought calls of it that are not tail calls is entered there, if
   it can be: they would otherwise stay calls of another function, which no
   turn of [fd]'s machine takes.  [None] where some partner is not spliced
   so, or where one's body would need instantiating there
   ({!splice_partners}).  A function that does not recurse once spliced
   into makes no loop a copy would serve: it is left as it is.  [defs]
   are the program's definitions. *)
let splice_member ~inlines ~defs ~members fd =
  let self = fd.fd_ref in
  let own_vars = Mlutil.type_maxvar fd.fd_type in
  let own_monad = Ml_type_util.codomain_monad fd.fd_type in
  let partner g = (not (Common.globref_equal g self)) && List.exists (Common.globref_equal g) members in
  let enterable def =
    inlines self && yields_alike fd.fd_type def.fd_type && calls_back ~defs ~self def <> []
    && calls_itself_in_flow ~defs def
    && not (definition_suspends self fd.fd_type fd.fd_body)
  in
  let rec go opaque inlined entered body =
    let current = {fd with fd_body = body} in
    let flow = flow_of self current in
    let next pending =
      Option.bind flow (next_inlining ~opaque ~effects:(definition_effects current) ~defs ~pending self)
    in
    let spliced g = List.exists (Common.globref_equal g) inlined in
    let finished = Some (List.rev inlined, entered, body) in
    match next (fun g -> partner g && not (spliced g)) with
    | None -> (
      match next spliced with
      | Some {partner; continued = []; invoked = _ :: _ as invoked} when entered = None -> (
        let def = Ref.User.Map.find partner defs in
        if not (enterable def) then finished
        else
          match adopt_calls def invoked body with
          | Ok (body, o) -> go opaque inlined (Some o) body
          | Error _ -> finished )
      | Some _ | None -> finished )
    | Some {partner; continued; invoked} -> (
      let def = Ref.User.Map.find partner defs in
      if Mlutil.type_maxvar def.fd_type <> own_vars then unspliced "variables" self
      else if not (Option.equal Names.GlobRef.UserOrd.equal (Ml_type_util.codomain_monad def.fd_type) own_monad) then
        unspliced "monad" self
      else if Option.is_empty (flow_of partner (Ref.User.Map.find partner defs)) then unspliced "suspended" self
      else if invoked <> [] && not (inlines self) then unspliced "invoked" self
      else
        let spliced =
          Result.bind (splice_calls def continued body) (fun (body, _) ->
              if invoked = [] then Ok (body, entered, [])
              else if entered = None && enterable def then
                Result.map (fun (body, o) -> (body, Some o, [])) (adopt_calls def invoked body)
              else Result.map (fun (body, run) -> (body, entered, run)) (splice_calls def invoked body) )
        in
        match spliced with
        | Ok (body, entered, run) -> go (opaque @ run) (partner :: inlined) entered body
        | Error why -> unspliced why self )
  in
  match go [] [] None fd.fd_body with
  | Some ((_ :: _), _, body) when not (recurses {fd with fd_body = body}) -> Some ([], None, fd.fd_body)
  | spliced -> spliced

let splice_partners ~loopified ~inlines ({structure = struc; splices} : Core_phase.normalizing) : Core_phase.normalizing =
  let groups = Recursive_groups.analyze struc in
  let originals = ref Ref.User.Map.empty in
  Modutil.struct_iter
    (fun d -> List.iter (fun fd -> originals := Ref.User.Map.add fd.fd_ref fd !originals) (Mlutil.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let defs = !originals in
  let splicings =
    Ref.User.Map.filter_map
      (fun r fd ->
        match Recursive_groups.group groups r with
        | Some members when loopified r && (not (Table.is_custom r)) && not (Splices.decided splices r) ->
          Some (splice_member ~inlines ~defs ~members fd)
        | Some _ | None -> None )
      defs
  in
  (* A group is spliced whole or not at all: a member declines where a
     partner's body cannot stand in its own, and a partner spliced instead
     would take its body, with the call it could not splice, into its own --
     a call of the partner at another instance, say, which no loop of the
     partner can take. *)
  let declined r =
    List.exists
      (fun m -> match Ref.User.Map.find_opt m splicings with Some None -> true | Some (Some _) | None -> false)
      (Option.default [] (Recursive_groups.group groups r))
  in
  (* Each member decided: the copy its machine enters, if any, and its
     spliced body, if it changes. *)
  let decision r = function
    | Some (_ :: _, _, _) when declined r -> unspliced "group" r
    | Some (_ :: _, entered, body) ->
      Probe.hit "SPLICE_spliced" (fun () -> Table.kername_of_global r);
      Some (entered, Some body)
    | Some ([], _, _) -> Some (None, None)
    | None -> None
  in
  let decisions = Ref.User.Map.filter_map decision splicings in
  let splice fd =
    match Ref.User.Map.find_opt fd.fd_ref decisions with
    | Some (_, Some body) -> {fd with fd_body = body}
    | Some (_, None) | None -> fd
  in
  { structure =
      Modutil.map_struct_decls
        (function
          | Dfix fds -> Dfix (List.map splice fds)
          | Dterm (r, b, ty) ->
            let fd = splice {fd_ref = r; fd_body = b; fd_type = ty} in
            Dterm (r, fd.fd_body, ty)
          | d -> d )
        struc;
    splices = Ref.User.Map.fold (fun r (entered, _) s -> Splices.decide ?entered r s) decisions splices }

(* A member of a group recurses by the calls of itself it makes, those in
   the copies of its partners spliced into its body included
   ({!splice_partners}), and only those: a partner's call that was not
   spliced stays a call of another function.  A function on no cycle calls
   no function it could recurse through. *)
let analyze groups program =
  let struc = Core_phase.structure program in
  let effects = Core_effects.analyze struc in
  let defs = ref Ref.User.Map.empty in
  let add fd = defs := Ref.User.Map.add fd.fd_ref fd !defs in
  Modutil.struct_iter
    (fun d -> List.iter add (Mlutil.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let defs = !defs in
  (* A function is generated taking every parameter its type declares, its
     body applied to those it does not bind ({!Core_elaborate.declaration_scope}):
     its calls are read there, a call with fewer arguments than that being
     the closure the C++ makes of it. *)
  (* A member's own calls: what a loop of the member can take. *)
  let member_kind r fd =
    let callee ~depth:_ = function
      | MLglob use when Names.GlobRef.UserOrd.equal use.callee r -> Some (fd_parameters fd)
      | _ -> None
    in
    classify ~effects ~callee (snd (Core_elaborate.declaration_scope fd.fd_type fd.fd_body))
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
    Ref.User.Map.fold
      (fun r fd m ->
        let member ~within:_ ~depth:_ = function
          | MLglob use when Names.GlobRef.UserOrd.equal use.callee r -> Some 0
          | _ -> None
        in
        match Ref.User.Map.find_opt r kinds with
        | Some Nontail -> (
          match modulo_cons_chains ~effects ~member ~bodies:[|fd.fd_body|] 0 with
          | Some chains -> Ref.User.Map.add r chains m
          | None -> m )
        | Some (Tail | No_recursion) | None -> m )
      defs Ref.User.Map.empty
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
        let rec targets = function
          | MLmagic (_, e) -> targets e
          | MLapp (MLglob use, args)
            when List.exists (Common.globref_equal use.callee) members
                 && List.length args >= parameters defs use.callee ->
            [{target = Function use.callee; occurrence = Global_use.occurrence use}]
          | _ -> []
        in
        let lex, body = Core_elaborate.declaration_scope fd.fd_type fd.fd_body in
        resumes_of ~effects ~entered:(Splices.is_entered_copy (Core_phase.splices program)) ~origin:r ~targets lex body )
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
        let lex, body = Core_elaborate.declaration_scope fd.fd_type fd.fd_body in
        flow_fixpoints ~names (Lexenv.depth lex) body )
      defs
  in
  let calls =
    List.fold_left
      (fun m g ->
        let uses = ref [] in
        let rec walk = function
          | MLglob use when List.exists (Common.globref_equal use.callee) g.members ->
            uses := (use.callee, Global_use.occurrence use) :: !uses
          | e -> Mlutil.ast_iter walk e
        in
        List.iter (fun r -> Option.iter (fun fd -> walk fd.fd_body) (Ref.User.Map.find_opt r defs)) g.members;
        List.fold_left
          (fun m r ->
            Ref.User.Map.add r
              (List.rev (List.filter_map (fun (c, o) -> if Common.globref_equal c r then Some o else None) !uses))
              m )
          m g.members )
      Ref.User.Map.empty plans
  in
  { groups = plans;
    by_member;
    defined;
    locals = local_groups ~effects defs;
    modulo_cons;
    suspended;
    resumes;
    adoptable;
    kinds;
    calls;
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
         && List.equal (List.equal Occurrence.equal) l.calls l'.calls
         && List.equal Bool.equal l.named l'.named
         && List.equal Occurrence.equal l.entered l'.entered )
       a.locals b.locals
  && Ref.User.Map.equal same_chains a.modulo_cons b.modulo_cons
  && Ref.User.Set.equal a.suspended b.suspended
  && Ref.User.Map.equal
       (List.equal (fun r r' ->
            Core_binder.equal r.binder r'.binder
            && Core_binder.same_site r.binder r'.binder
            && List.equal Core_binder.equal r.live r'.live
            && List.equal same_call r.after r'.after
            && List.equal
                 (fun p p' ->
                   Core_binder.equal p.passed p'.passed && Core_binder.equal p.into p'.into && same_call p.call p'.call )
                 r.passes r'.passes
            && List.equal Core_binder.equal r.read_by_call r'.read_by_call
            && List.equal
                 (fun c c' -> Core_binder.equal c.recomputed c'.recomputed && List.equal Core_binder.equal c.from c'.from)
                 r.recomputable r'.recomputable ) )
       a.resumes b.resumes
  && Ref.User.Map.equal (List.equal Occurrence.equal) a.adoptable b.adoptable
  && Ref.User.Map.equal ( = ) a.kinds b.kinds
  && Ref.User.Map.equal (List.equal Occurrence.equal) a.calls b.calls
  && List.equal Occurrence.equal a.let_lambdas b.let_lambdas

(* Whether some member of the group of [r] suspends. *)
let suspends t r =
  let members = match Ref.User.Map.find_opt r t.by_member with Some g -> g.members | None -> [r] in
  List.exists (fun m -> Ref.User.Set.mem m t.suspended) members

let tail_loops t =
  let functions =
    Ref.User.Map.fold (fun r kind acc -> if kind = Tail && not (suspends t r) then r :: acc else acc) t.kinds []
  in
  let locals =
    List.filter_map
      (fun (l : local_group) ->
        if l.local_kind = Tail && (not l.suspends) && List.length l.chains = 1 then Some l.occurrence else None )
      t.locals
  in
  (List.rev functions, locals)

let frame_loops t =
  let functions =
    Ref.User.Map.fold
      (fun r kind acc ->
        if kind = Nontail && (not (suspends t r)) && not (Ref.User.Map.mem r t.modulo_cons) then r :: acc else acc )
      t.kinds []
  in
  let locals =
    List.filter_map
      (fun (l : local_group) ->
        match l.chains with
        | [(None | Some [])] when l.local_kind = Nontail && not l.suspends -> Some l.occurrence
        | _ -> None )
      t.locals
  in
  (List.rev functions, locals)

let modulo_cons_loops t =
  let functions = Ref.User.Map.fold (fun r _ acc -> if suspends t r then acc else r :: acc) t.modulo_cons [] in
  let locals =
    List.filter_map
      (fun (l : local_group) ->
        match l.chains with
        | [Some (_ :: _)] when l.local_kind = Nontail && not l.suspends -> Some l.occurrence
        | _ -> None )
      t.locals
  in
  (List.rev functions, locals)

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

(* A member's kind is its own calls'.  It suspends where some member of its
   group does, whose body may be spliced into its own. *)
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

let adoptable_in t r = Option.default [] (Ref.User.Map.find_opt r t.adoptable)

let adoptable r = adoptable_in !installed r

(* Copies of a fixpoint share its occurrence, and plan alike. *)
let adoptable_at (occurrence, member) =
  List.find_map
    (fun (l : local_group) ->
      if Occurrence.equal l.occurrence occurrence then List.nth_opt l.adoptable member else None )
    !installed.locals
  |> Option.default []

let adoptable_by_fixpoint ~lifted occurrence =
  List.exists
    (fun (l : local_group) ->
      List.exists (Occurrence.equal l.occurrence) lifted
      && List.exists (List.exists (Occurrence.equal occurrence)) l.adoptable )
    !installed.locals

let adoptable_somewhere ~lifted occurrence =
  Ref.User.Map.exists (fun _ os -> List.exists (Occurrence.equal occurrence) os) !installed.adoptable
  || adoptable_by_fixpoint ~lifted occurrence

let calls r = Option.default [] (Ref.User.Map.find_opt r !installed.calls)

(* Copies of a fixpoint share its occurrence, and so do their calls. *)
let member_calls (occurrence, member) =
  List.concat_map
    (fun (l : local_group) ->
      if Occurrence.equal l.occurrence occurrence then Option.default [] (List.nth_opt l.calls member)
      else [] )
    !installed.locals

let named_as_value (occurrence, member) =
  List.exists
    (fun (l : local_group) -> Occurrence.equal l.occurrence occurrence && List.nth_opt l.named member = Some true)
    !installed.locals

let entering occurrence =
  member_calls (occurrence, 0)
  @ List.concat_map
      (fun (l : local_group) -> if Occurrence.equal l.occurrence occurrence then l.entered else [])
      !installed.locals

let resumes_binding (b : Core_binder.t) =
  match Ref.User.Map.find_opt b.origin !installed.resumes with
  | Some rs -> List.filter (fun r -> Core_binder.equal r.binder b && Core_binder.same_site r.binder b) rs
  | None -> []

(* A lambda a let binds does not call itself. *)
let strategy_of_let occurrence =
  if List.exists (Occurrence.equal occurrence) !installed.let_lambdas then Some No_loop else None
