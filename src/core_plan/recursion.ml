(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)


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
  occurrence : Core.Occurrence.t;  (* the fixpoint's *)
  local_kind : kind;  (* the group's, as the member that recurses most *)
  chains : chain list option list;
      (* per member, its chains, if it recurses through no other call that
         is not a tail call *)
  suspends : bool;  (* some member's body suspends ({!suspends_within}) *)
  adoptable : Core.Occurrence.t list list;  (* per member, {!flow_fixpoints} calling the group *)
  calls : Core.Occurrence.t list list;
      (* per member, the reads heading its calls in the group's bodies *)
  named : bool list;  (* per member, whether the group's bodies read it other than at a call's head *)
  entered : Core.Occurrence.t list;
      (* the calls of the member the fixpoint stands for made where it is
         bound: the fixpoint applied, or the reads of the let binding it *)
}

(* The calls of one partner a function inlines: those that continue in the
   partner's body, and those that run it in their place. *)
type inlining = {
  partner : Names.GlobRef.t;
  continued : Core.Occurrence.t list;
  invoked : Core.Occurrence.t list;
}

(* A call a function resumes after. *)
type target =
  | Function of Names.GlobRef.t
  | Member of Core.Occurrence.t * int
  | Entering of Core.Occurrence.t

(* A call a function resumes after, and the occurrence it is made of: the
   global's use, the read of the member at its head, or the fixpoint
   applied. *)
type call = {
  target : target;
  occurrence : Core.Occurrence.t;
}

(* Where a function goes on once a recursive call returns: the binder the
   call's result is bound to, the binders bound before it that what follows
   reads, which a frame keeps across the call, the calls it resumes after,
   those of the live binders the calls' arguments read, and the binders in
   scope whose value makes no call, with those it reads. *)
type resume = {
  binder : Core.Binder.t;
  live : Core.Binder.t list;
  after : call list;
  passes : passing list;
  read_by_call : Core.Binder.t list;
  recomputable : recomputable list;
}

(* A live binder passed on, as it is, for a parameter of a recursive call. *)
and passing = {
  passed : Core.Binder.t;
  into : Core.Binder.t;
  call : call;
}

(* A binder whose value makes no call, and the binders it reads. *)
and recomputable = {
  recomputed : Core.Binder.t;
  from : Core.Binder.t list;
}

type t = {
  groups : group list;  (* one per recursive group *)
  by_member : group Core.Ref.User.Map.t;  (* each member's group *)
  defined : Core.Ref.User.Set.t;  (* every function the program defines *)
  locals : local_group list;  (* one per local fixpoint, copies included *)
  modulo_cons : chain list Core.Ref.User.Map.t;
      (* per definition that recurses by some call that is not a tail call,
         its chains, if every such call is the one call of a chain *)
  suspended : Core.Ref.User.Set.t;  (* the definitions whose body suspends *)
  resumes : resume list Core.Ref.User.Map.t;  (* per definition, its resume points *)
  adoptable : Core.Occurrence.t list Core.Ref.User.Map.t;  (* per definition, {!flow_fixpoints} calling its group *)
  kinds : kind Core.Ref.User.Map.t;  (* per definition, its own calls *)
  calls : Core.Occurrence.t list Core.Ref.User.Map.t;  (* per member, the uses heading its calls in its group's bodies *)
  let_lambdas : Core.Occurrence.t list;  (* the lets binding a lambda *)
}

let empty =
  { groups = [];
    by_member = Core.Ref.User.Map.empty;
    defined = Core.Ref.User.Set.empty;
    locals = [];
    modulo_cons = Core.Ref.User.Map.empty;
    suspended = Core.Ref.User.Set.empty;
    resumes = Core.Ref.User.Map.empty;
    adoptable = Core.Ref.User.Map.empty;
    kinds = Core.Ref.User.Map.empty;
    calls = Core.Ref.User.Map.empty;
    let_lambdas = [] }

(* The number of lambdas heading a term, plus [n], and the body under them. *)
let rec split_params n = function
  | Core.Expr.Lambda {body = b; _} -> split_params (n + 1) b
  | b -> (n, b)

(* The effect operation [use] is, where [effects] says it is generated
   sequentially: a bind's continuation and a ret's value then stand where
   the operation does. *)
let sequential effects use =
  match Effects.lookup effects use with
  | Some {Effects.operation; mode = Effects.Sequential} -> Some operation
  | Some _ | None -> None

(* A custom whose replacement text is its one argument writes nothing
   around it, so the argument is where the custom is: sequential [itree]
   maps [go] and [TauF] so, and [Tau t] is [t]. *)
let identity r =
  Base.Table.is_custom r && Cpp_ir.Foreign.shape_of_text (Base.Table.find_custom r) = Identity

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
    | Core.Expr.Construct {constructor = c; arguments = [a]; _} when identity c -> walk ~tail a
    | Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = [a]} when identity use.callee && Base.Table.to_inline use.callee ->
      walk ~tail a
    | Core.Expr.Apply {callee = f; arguments = args} when Option.has_some (callee ~depth f) ->
      List.iter (walk ~tail:false) args;
      let n = List.length args and parameters = Option.get (callee ~depth f) in
      if n < parameters then ()
      else if tail && n = parameters then tail_call := true
      else nontail_call := true
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Bind -> (
      (* The action runs, and the continuation's body goes on where the bind
         stands. *)
      match List.rev args with
      | k :: action :: rest ->
        List.iter (walk ~tail:false) rest;
        walk ~tail:false action;
        continuation ~depth ~tail k
      | _ -> List.iter (walk ~tail:false) args )
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Return -> (
      match List.rev args with
      | value :: rest ->
        List.iter (walk ~tail:false) rest;
        walk ~tail value
      | [] -> () )
    | Core.Expr.Apply {callee = (Core.Expr.Lambda _ as f); arguments = args} ->
      List.iter (walk ~tail:false) args;
      let rec enter entered n = function
        | Core.Expr.Lambda {body = b; _} when n > 0 -> enter (entered + 1) (n - 1) b
        | b -> walk_under entered ~tail:(tail && n = 0) b
      in
      enter 0 (List.length args) f
    | Core.Expr.Apply {callee = f; arguments = args} ->
      walk ~tail:false f;
      List.iter (walk ~tail:false) args
    | Core.Expr.Let {value = a; body = b; _} ->
      walk ~tail:false a;
      walk_under 1 ~tail b
    | Core.Expr.Match {scrutinee = s; branches; _} ->
      walk ~tail:false s;
      Array.iter (fun {Core.Match.Branch.binders = ids; body = b; _} -> walk_under (List.length ids) ~tail b) branches
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} ->
      walk ~tail a
    | Core.Expr.Lambda _ -> ()
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      Array.iter
        (fun f ->
          let n, b = split_params 0 f in
          walk_under (Array.length ids + n) ~tail:false b )
        bodies
    | Core.Expr.Construct {arguments = l; _} | Core.Expr.Tuple l -> List.iter (walk ~tail:false) l
    | Core.Expr.Persistent_array {elements = a; default = d} ->
      Array.iter (walk ~tail:false) a;
      walk ~tail:false d
    | Core.Expr.Bound_variable _
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ ->
      ()
  and continuation ~depth ~tail = function
    | Core.Expr.Lambda _ as k ->
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
   of, as {!Cpp_passes.Temporaries} restores it for the transform that reads
   constructors around calls. *)
let rec restore_temporaries e =
  match e with
  | Core.Expr.Let {binder = (Core.Binder_name.Generated _ as id);
                   binder_type = ty;
                   value = rhs;
                   body;
                   occurrence = occ} ->
    let rhs = restore_temporaries rhs and body = restore_temporaries body in
    let reads = ref 0 in
    Base.Core_util.ast_iter_rel_applied (fun n i _ -> if i = n + 1 then incr reads) body;
    if !reads = 1 then Base.Core_util.ast_subst rhs body else Core.Expr.Let {binder = id;
                                                                     binder_type = ty;
                                                                     value = rhs;
                                                                     body;
                                                                     occurrence = occ}
  | e -> Base.Core_util.ast_map restore_temporaries e

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
      | Core.Expr.Apply {callee = f; arguments = args} when Option.has_some (reached ~depth f) ->
        List.fold_left (fun n a -> n + calls ~depth a) 1 args
      | f when Option.has_some (reached ~depth f) -> 1
      | Core.Expr.Let {value = a; body = b; _} -> calls ~depth a + under 1 b
      | Core.Expr.Lambda {body = b; _} -> under 1 b
      | Core.Expr.Match {scrutinee = s; branches; _} ->
        Array.fold_left
          (fun n {Core.Match.Branch.binders = ids; body = b; _} -> n + under (List.length ids) b)
          (calls ~depth s) branches
      | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
        let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
        Array.fold_left (fun n b -> n + under (Array.length ids) b) 0 funs
      | e ->
        let n = ref 0 in
        Base.Core_util.ast_iter (fun c -> n := !n + calls ~depth c) e;
        !n
    in
    let full_call ~depth = function
      | Core.Expr.Apply {callee = f; arguments = args} -> (
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
      | Core.Expr.Construct {constructor; arguments = args; _} -> (
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
    | Core.Expr.Match {scrutinee = s; branches; _} ->
      general_if (calls ~depth s > 0);
      Array.iter (fun {Core.Match.Branch.binders = ids; body = b; _} -> walk_under (List.length ids) b) branches
    | Core.Expr.Let {value = a; body = b; _} ->
      general_if (calls ~depth a > 0);
      walk_under 1 b
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> general_if ((not (self_call ~depth a)) && calls ~depth a > 0)
    | Core.Expr.Construct {constructor = c; arguments = [a]; _} when identity c -> walk_under 0 a
    | Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = [a]} when identity use.callee && Base.Table.to_inline use.callee ->
      walk_under 0 a
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Bind -> (
      match List.rev args with
      | (Core.Expr.Lambda _ as k) :: action :: rest ->
        general_if (List.exists (fun a -> calls ~depth a > 0) (action :: rest));
        let n, b = split_params 0 k in
        walk_under n b
      | _ -> general_if (calls ~depth e > 0) )
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Return -> (
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
    Core.Lexenv.push
      (List.map
         (fun (x, ty) -> {Core.Lexenv.id = Base.Core_util.id_of_binder_name x; type_ = ty; role = Core.Lexenv.Value})
         ids )
      lex
  in
  match e with
  | Core.Expr.Lambda {parameter = x; parameter_type = ty; body = b} -> iter_scoped f (bind [(x, ty)] lex) b
  | Core.Expr.Let {binder = x; binder_type = ty; value = a; body = b; _} ->
    iter_scoped f lex a;
    iter_scoped f (bind [(x, ty)] lex) b
  | Core.Expr.Match {scrutinee = s; branches; _} ->
    iter_scoped f lex s;
    Array.iter (fun {Core.Match.Branch.binders = ids;
                     body = b; _} -> iter_scoped f (bind (List.rev ids) lex) b) branches
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    (* The last function of the group is the innermost binder. *)
    let lex = bind (List.rev_map (fun (g, ty) -> (Core.Binder_name.Source g, ty)) (Array.to_list ids)) lex in
    Array.iter (iter_scoped f lex) funs
  | e -> Base.Core_util.ast_iter (iter_scoped f lex) e

type suspension = {
  whole : Names.GlobRef.t -> Core.Type.t -> Core.Expr.t -> bool;
  at_constructor :
    self:Names.GlobRef.t option -> binder_type:(int -> Core.Type.t option) -> Names.GlobRef.t ->
    Core.Expr.t list -> bool;
}

(* Whether [e], standing in [lex] in the definition [self], suspends a
   coinductive constructor ({!suspension.at_constructor}) anywhere, under a
   lambda or in a local fixpoint's body too: the C++ [e] becomes holds the
   suspension wherever it stands. *)
let suspends_within ~suspension ~self lex e =
  let exception Found in
  try
    iter_scoped
      (fun lex -> function
        | Core.Expr.Construct {result_type = Core.Type.Global_app {head = n; _}; constructor = c; arguments = args; _}
          when (not (Base.Table.is_custom c))
               && suspension.at_constructor ~self:(Some self) ~binder_type:(Core.Lexenv.type_opt lex) n args ->
          raise Found
        | _ -> () )
      lex e;
    false
  with Found -> true

(* Whether the C++ the definition [self] of type [ty] becomes holds a
   suspension: it is suspended whole ({!suspension.whole}), or at a
   constructor. *)
let definition_suspends ~suspension self ty body =
  let lex, body = Elaborate.declaration_scope ty body in
  suspension.whole self (Base.Type_util.core_return_type ty) body || suspends_within ~suspension ~self lex body

(* The levels of the binders outside [e] that [e] reads as values, [e]
   standing under [depth] binders: one at a level of [heads] read only to
   call it is not. *)
let value_levels ~heads ~depth e =
  let found = ref [] in
  let rec go d = function
    | Core.Expr.Bound_variable {index = i; _} -> if i > d then found := (depth + d - i) :: !found
    | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; _};
                       arguments = args} when i > d && List.mem (depth + d - i) heads ->
      List.iter (go d) args
    | Core.Expr.Lambda {body = b; _} -> go (d + 1) b
    | Core.Expr.Let {value = a; body = b; _} ->
      go d a;
      go (d + 1) b
    | Core.Expr.Match {scrutinee = s; branches; _} ->
      go d s;
      Array.iter (fun {Core.Match.Branch.binders = ids; body = b; _} -> go (d + List.length ids) b) branches
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
      Array.iter (go (d + Array.length ids)) funs
    | e -> Base.Core_util.ast_iter (go d) e
  in
  go 0 e;
  List.sort_uniq Int.compare !found

(* The levels of [heads] [e], standing under [depth] binders, calls: the
   members of local fixpoints it enters again. *)
let called_heads ~heads ~depth e =
  let found = ref [] in
  let rec go d e =
    ( match e with
    | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; _}; _}
      when i > d && List.mem (depth + d - i) heads ->
      found := (depth + d - i) :: !found
    | _ -> () );
    match e with
    | Core.Expr.Lambda {body = b; _} -> go (d + 1) b
    | Core.Expr.Let {value = a; body = b; _} ->
      go d a;
      go (d + 1) b
    | Core.Expr.Match {scrutinee = s; branches; _} ->
      go d s;
      Array.iter (fun {Core.Match.Branch.binders = ids; body = b; _} -> go (d + List.length ids) b) branches
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
      Array.iter (go (d + Array.length ids)) funs
    | e -> Base.Core_util.ast_iter (go d) e
  in
  go 0 e;
  List.sort_uniq Int.compare !found

let rec strip =
  function Core.Expr.Coerce {value = e; _} | Core.Expr.Boxed_value {value = e; _}
    | Core.Expr.Lambda_group_barrier {value = e; _} -> strip e | e -> e

let in_place from into =
  match (Base.Core_util.type_simpl from, Base.Core_util.type_simpl into) with
  | Core.Type.Global_app {head = (Names.GlobRef.IndRef (kn, _) as r);
                          type_arguments = args; _}, Core.Type.Global_app {head = r'; type_arguments = args'; _}
    when Names.GlobRef.UserOrd.equal r r' -> (
    match Base.Table.get_ind_num_param_vars_opt kn with
    | Some n when List.length args >= n && List.length args' >= n ->
      List.for_all2 Base.Core_util.eq_core_type (CList.firstn n args) (CList.firstn n args')
    | Some _ | None -> false )
  | _ -> false

(* [e] through the coercions keeping its representation: the value a
   parameter is passed where the argument is [e]. *)
let rec as_passed = function
  | Core.Expr.Coerce {source_type = from; target_type = into; value = e; _} when in_place from into -> as_passed e
  | e -> e

(* The arguments a call is applied to, through coercions. *)
let rec arguments = function
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    arguments e
  | Core.Expr.Apply {arguments = args; _} -> args
  | _ -> []

(* Whether translation generates a match standing as a let's right-hand
   side as statements, each branch assigning the binder -- a custom match,
   or a record's -- rather than in a lambda invoked in place, as it does
   any other. *)
let match_bound_in_place ty branches = Match_kind.bound_in_place (Match_kind.classify ty branches)

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
  let binder level = Core.Binder.make ~origin ~level () in
  let dictionary level =
    match Core.Lexenv.binder lex (Core.Lexenv.depth lex - level) with
    | Some {role = Dictionary; _} -> true
    | Some {role = Value; _} | None -> false
  in
  let dedup_passings ps =
    let same p p' =
      Core.Binder.equal p.passed p'.passed && Core.Binder.equal p.into p'.into
      && Core.Occurrence.equal p.call.occurrence p'.call.occurrence
    in
    List.fold_left (fun acc p -> if List.exists (same p) acc then acc else acc @ [p]) [] ps
  in
  (* The parameter the [i]th argument of the recursive call [c] is passed
     for: the [i]th of the function's, or of the fixpoint's member, its
     members bound from level [first] of [fixpoints] on. *)
  let into ~fixpoints (c : call) i =
    match c.target with
    | Function g -> Some (Core.Binder.make ~origin:g ~level:i ())
    | Member (o, _) ->
      Option.map
        (fun (first, n) -> binder (first + n + i))
        (List.find_map (fun (o', fn) -> if Core.Occurrence.equal o o' then Some fn else None) fixpoints)
    | Entering _ -> None
  in
  (* The live binders [rest], standing under [depth] binders, passes on to
     a recursive call [targets] names that enters the machine: one whose
     value is what a let or a bind binds, or what [rest] returns.  A call
     whose value goes into some other term stays a call.  A call of a local
     fixpoint's member passes on what the fixpoint captures as well: a
     machine adopting it enters it with its captures, each the binder it
     names. *)
  let passings ~fixpoints ~captures ~targets ~live depth rest =
    let found = ref [] in
    let rec go ~enters d e =
      ( match targets ~depth:(depth + d) e with
      | [c] when enters ->
        List.iteri
          (fun i a ->
            match as_passed a with
            | Core.Expr.Bound_variable {index = j; _} when j > d && List.mem (depth + d - j) live ->
              Option.iter
                (fun p -> found := {passed = binder (depth + d - j); into = p; call = c} :: !found)
                (into ~fixpoints c i)
            | _ -> () )
          (arguments e);
        ( match c.target with
        | Member (o, _) ->
          let captured =
            Option.default [] (List.find_map (fun (o', l) -> if Core.Occurrence.equal o o' then Some l else None) captures)
          in
          List.iter
            (fun l -> if List.mem l live then found := {passed = binder l; into = binder l; call = c} :: !found)
            captured
        | Function _ | Entering _ -> () )
      | _ -> () );
      match e with
      | Core.Expr.Lambda _ | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ -> ()
      | Core.Expr.Let {value = a; body = b; _} ->
        go ~enters:true d a;
        go ~enters (d + 1) b
      | Core.Expr.Match {scrutinee = s; branches; _} ->
        go ~enters:false d s;
        Array.iter (fun {Core.Match.Branch.binders = ids; body = b; _} -> go ~enters (d + List.length ids) b) branches
      | Core.Expr.Coerce {value = e; _}
      | Core.Expr.Boxed_value {value = e; _}
      | Core.Expr.Lambda_group_barrier {value = e; _} ->
        go ~enters d e
      | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Bind -> (
        match List.rev args with
        | Core.Expr.Lambda {body = k; _} :: action :: others ->
          go ~enters:true d action;
          List.iter (go ~enters:false d) others;
          go ~enters (d + 1) k
        | _ -> List.iter (go ~enters:false d) args )
      | e -> Base.Core_util.ast_iter (go ~enters:false d) e
    in
    go ~enters:true 0 rest;
    List.rev !found
  in
  (* The levels [e], standing under [depth] binders, reads as values: those
     {!value_levels} finds, and what a local fixpoint whose member [e] calls
     captures -- calling it enters the machine again with them: [go rest
     (e :: x)] reads [r] through [go]. *)
  let reads ~heads ~fixpoints ~captures depth e =
    let captured_by_called =
      List.concat_map
        (fun h ->
          match List.find_opt (fun (_, (first, n)) -> first <= h && h < first + n) fixpoints with
          | Some (occ, _) ->
            Option.default []
              (List.find_map (fun (o, l) -> if Core.Occurrence.equal o occ then Some l else None) captures)
          | None -> [] )
        (called_heads ~heads ~depth e)
    in
    value_levels ~heads ~depth e @ captured_by_called
  in
  (* A local the frames of consecutive points keep is kept alike in all of
     them, each handler passing it to the next frame as it holds it: what
     follows a point passes it on as what follows the outermost of them,
     [enclosing], does too.  What the term the point stands in is the
     right-hand side of reads once it is done ([awaited]) the frame keeps as
     well: the handler runs that too, and pushes the frame of a point there,
     which holds it as that point's continuation does -- passed on by
     pointer only if that passes it so ([inherited]). *)
  let resume ~heads ~fixpoints ~captures ~targets ~enclosing ~awaited ~sites ~site ~after ~arguments_read ~recipes depth rest =
    let live =
      List.filter
        (fun l -> l <> depth && not (dictionary l))
        (List.sort_uniq Int.compare (reads ~heads ~fixpoints ~captures (depth + 1) rest @ awaited))
    in
    (* A live binder a let, a bind or a pattern introduces is named with
       its site: the backend may have another binder of its level in scope
       where it keeps it, a pattern variable of a match whose continuation
       it runs in that match's branch. *)
    let live_binders =
      List.map (fun l -> Core.Binder.make ~origin ~level:l ?site:(List.assoc_opt l sites) ()) live
    in
    let inherited =
      List.concat_map
        (fun r -> List.filter (fun q -> List.exists (Core.Binder.equal q.passed) live_binders) r.passes)
        enclosing
    in
    let r =
      { binder = Core.Binder.make ~origin ~level:depth ~site:(Binding site) ();
        live = live_binders;
        after;
        passes =
          dedup_passings
            (inherited
             @ passings ~fixpoints ~captures ~targets ~live:(List.filter (fun l -> not (List.mem l awaited)) live)
                 (depth + 1) rest);
        read_by_call = List.map binder (List.filter (fun l -> List.mem l arguments_read) live);
        recomputable =
          List.filter_map
            (fun (l, reads) ->
              if dictionary l then None
              else Some {recomputed = binder l;
                         from = List.map binder (List.filter (fun r -> not (dictionary r)) reads)} )
            recipes }
    in
    found := r :: !found;
    r
  in
  let rec walk ~targets ~heads ~fixpoints ~enclosing ~awaited ~closures ~fields ~captures ~sites depth e =
    (* A local fixpoint applied where it is written, reaching a recursive
       call, is bound as one ({!Normalize}). *)
    let rec reaches depth e =
      targets ~depth e <> []
      ||
      match e with
      | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
        let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
        Array.exists
          (fun f ->
            let arity, b = split_params 0 f in
            reaches (depth + Array.length ids + arity) b )
          funs
      | Core.Expr.Lambda _ -> false
      | Core.Expr.Let {value = a; body = b; _} -> reaches depth a || reaches (depth + 1) b
      | Core.Expr.Match {scrutinee = s; branches; _} ->
        reaches depth s
        || Array.exists (fun (br : Core.Match.Branch.t) -> reaches (depth + List.length br.binders) br.body) branches
      | e ->
        let found = ref false in
        Base.Core_util.ast_iter (fun c -> if reaches depth c then found := true) e;
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
        | Core.Expr.Apply
          {callee = (Core.Expr.Fixpoint {occurrence = occ; _} | Core.Expr.Cofixpoint {occurrence = occ; _} as fix); _}
          when reaches depth fix ->
          [{target = Entering occ; occurrence = occ}]
        | Core.Expr.Match {scrutinee_type = ty; branches; _} when match_bound_in_place ty branches ->
          List.concat_map
            (fun {Core.Match.Branch.binders = ids; body = b; _} -> ending (depth + List.length ids) b)
            (Array.to_list branches)
        | Core.Expr.Let {body = b; _} -> ending (depth + 1) b
        | Core.Expr.Coerce {value = b; _}
        | Core.Expr.Boxed_value {value = b; _}
        | Core.Expr.Lambda_group_barrier {value = b; _} ->
          ending depth b
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
          Option.default []
            (List.find_map (fun (o', l) -> if Core.Occurrence.equal o o' then Some l else None) captures)
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
        | Core.Expr.Apply {callee = (Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ as fix);
                           arguments = args} when reaches depth fix ->
          through_closures [] (value_levels ~heads ~depth fix) @ calls_read depth [] args
        | Core.Expr.Match {scrutinee_type = ty; branches; _} when match_bound_in_place ty branches ->
          List.concat_map
            (fun {Core.Match.Branch.binders = ids; body = b; _} -> arguments_read (depth + List.length ids) b)
            (Array.to_list branches)
        | Core.Expr.Let {body = b; _} -> arguments_read (depth + 1) b
        | Core.Expr.Coerce {value = b; _}
        | Core.Expr.Boxed_value {value = b; _}
        | Core.Expr.Lambda_group_barrier {value = b; _} ->
          arguments_read depth b
        | _ -> [] )
    in
    let go = walk ~targets ~heads ~fixpoints ~enclosing ~awaited ~closures ~fields ~captures ~sites in
    (* The body of the [i]th branch of the match [occ], binding [ids] from
       [depth] on. *)
    let go_branch occ depth i ids b =
      let sites = List.mapi (fun k _ -> (depth + k, Core.Binder.Branch (occ, i))) ids @ sites in
      walk ~targets ~heads ~fixpoints ~enclosing ~awaited ~closures ~fields ~captures ~sites (depth + List.length ids) b
    in
    (* [e] at [depth] with what [k], standing under [n] binders more, reads
       of the binders outside it awaited too: a point in [e] resumes into
       [k]. *)
    let go_then depth e n k =
      let outside = List.filter (fun l -> l < depth) (reads ~heads ~fixpoints ~captures (depth + n) k) in
      walk ~targets ~heads ~fixpoints ~enclosing ~awaited:(outside @ awaited) ~closures ~fields ~captures ~sites depth e
    in
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
      | after ->
        resume ~heads ~fixpoints ~captures ~targets ~enclosing ~awaited ~sites ~site ~after ~arguments_read ~recipes depth rest
        :: enclosing
    in
    match e with
    | Core.Expr.Let {value = a; body = b; occurrence = site; _} ->
      let enclosing = resuming ~site ~after:(ending depth a) ~arguments_read:(arguments_read depth a) depth b in
      go_then depth a 1 b;
      let rec closure = function
        | Core.Expr.Lambda _ | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ -> true
        | Core.Expr.Coerce {value = e; _}
        | Core.Expr.Boxed_value {value = e; _}
        | Core.Expr.Lambda_group_barrier {value = e; _} -> closure e
        | _ -> false
      in
      let closures = if closure a then (depth, a) :: closures else closures in
      (* The let binding a partner's copy the machine enters: its calls in
         the body are the copy's, a member of the fixpoint at that level. *)
      let targets, heads, fixpoints, captures =
        match a with
        | Core.Expr.Fixpoint {members = [|_|]; occurrence = occ; _} when entered occ ->
          let level = depth in
          let rec entering ~depth:d = function
            | Core.Expr.Coerce {value = e; _}
            | Core.Expr.Boxed_value {value = e; _}
            | Core.Expr.Lambda_group_barrier {value = e; _} ->
              entering ~depth:d e
            | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = k;
                                                                  occurrence = read}; _} when d - k = level ->
              [{target = Member (occ, 0); occurrence = read}]
            | e -> targets ~depth:d e
          in
          (entering, level :: heads, (occ, (depth, 1)) :: fixpoints, (occ, value_levels ~heads ~depth a) :: captures)
        | _ -> (targets, heads, fixpoints, captures)
      in
      let sites = (depth, Core.Binder.Binding site) :: sites in
      walk ~targets ~heads ~fixpoints ~enclosing ~awaited ~closures ~fields ~captures ~sites (depth + 1) b
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Bind -> (
      match List.rev args with
      | Core.Expr.Lambda {body = k; _} :: action :: rest ->
        let after = targets ~depth action in
        let arguments_read = if after = [] then [] else calls_read depth after (arguments action) in
        let enclosing = resuming ~site:(Core.Global_use.occurrence use) ~after ~arguments_read depth k in
        go_then depth action 1 k;
        List.iter (go depth) rest;
        let sites = (depth, Core.Binder.Binding (Core.Global_use.occurrence use)) :: sites in
        walk ~targets ~heads ~fixpoints ~enclosing ~awaited ~closures ~fields ~captures ~sites (depth + 1) k
      | _ -> List.iter (go depth) args )
    | Core.Expr.Match {scrutinee_type = ty;
                       scrutinee = s;
                       branches = [|{Core.Match.Branch.binders = ids;
                                     body = b; _}|]; occurrence = occ; _} when Base.Table.record_fields_of_type ty <> [] -> (
      go depth s;
      match strip s with
      | Core.Expr.Bound_variable {index = i; _} ->
        let n = List.length ids in
        let fields = List.init n (fun k -> (depth + k, depth - i)) @ fields in
        let sites = List.init n (fun k -> (depth + k, Core.Binder.Branch (occ, 0))) @ sites in
        walk ~targets ~heads ~fixpoints ~enclosing ~awaited ~closures ~fields ~captures ~sites (depth + n) b
      | _ -> go_branch occ depth 0 ids b )
    | Core.Expr.Match {scrutinee = s; branches; occurrence = occ; _} ->
      go depth s;
      Array.iteri (fun i {Core.Match.Branch.binders = ids; body = b; _} -> go_branch occ depth i ids b) branches
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group
      and funs = Core.Recursion.Group.bodies rec_group
      and occ = rec_group.occurrence in
      (* The member [m] is bound at level [depth + m], the last innermost. *)
      let first = depth and n = Array.length ids in
      let rec member ~depth = function
        | Core.Expr.Coerce {value = e; _}
        | Core.Expr.Boxed_value {value = e; _}
        | Core.Expr.Lambda_group_barrier {value = e; _} ->
          member ~depth e
        | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = k; occurrence = read}; _} when first <= depth - k
          && depth - k < first + n ->
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
          walk ~targets ~heads ~fixpoints ~enclosing:[] ~awaited:[] ~closures ~fields ~captures ~sites (depth + n + arity) b )
        funs
    | Core.Expr.Lambda {body = b; _} ->
      walk ~targets:(fun ~depth:_ _ -> []) ~heads:[] ~fixpoints ~enclosing:[] ~awaited:[] ~closures ~fields ~captures ~sites
        (depth + 1) b
    | e -> Base.Core_util.ast_iter (go depth) e
  in
  walk ~targets:(fun ~depth:_ e -> targets e) ~heads:[] ~fixpoints:[] ~enclosing:[] ~awaited:[] ~closures:[] ~fields:[] ~captures:[]
    ~sites:[] (Core.Lexenv.depth lex) body;
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
    | Core.Expr.Lambda {body = b; _} -> mentions (depth + 1) b
    | Core.Expr.Let {value = a; body = b; _} -> mentions depth a || mentions (depth + 1) b
    | Core.Expr.Match {scrutinee = s; branches; _} ->
      mentions depth s
      || Array.exists (fun {Core.Match.Branch.binders = ids;
                            body = b; _} -> mentions (depth + List.length ids) b) branches
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
      Array.exists (mentions (depth + Array.length ids)) funs
    | e ->
      let found = ref false in
      Base.Core_util.ast_iter (fun c -> if mentions depth c then found := true) e;
      !found
  in
  let found = ref [] in
  let rec flow depth = function
    | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group
      and funs = Core.Recursion.Group.bodies rec_group
      and occ = rec_group.occurrence in
      if Array.exists (mentions (depth + Array.length ids)) funs then found := occ :: !found
    | Core.Expr.Lambda _ -> ()
    | Core.Expr.Let {value = a; body = b; _} ->
      flow depth a;
      flow (depth + 1) b
    | Core.Expr.Match {scrutinee = s; branches; _} ->
      flow depth s;
      Array.iter (fun {Core.Match.Branch.binders = ids; body = b; _} -> flow (depth + List.length ids) b) branches
    | e -> Base.Core_util.ast_iter (flow depth) e
  in
  flow depth body;
  List.rev !found

(* [f depth e'] for [e] and every term [e'] in it, under [depth] binders
   more than [e]. *)
let rec iter_under f depth e =
  f depth e;
  match e with
  | Core.Expr.Lambda {body = b; _} -> iter_under f (depth + 1) b
  | Core.Expr.Let {value = a; body = b; _} ->
    iter_under f depth a;
    iter_under f (depth + 1) b
  | Core.Expr.Match {scrutinee = s; branches; _} ->
    iter_under f depth s;
    Array.iter (fun {Core.Match.Branch.binders = ids; body = b; _} -> iter_under f (depth + List.length ids) b) branches
  | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
    let ids = Core.Recursion.Group.functions rec_group and funs = Core.Recursion.Group.bodies rec_group in
    Array.iter (iter_under f (depth + Array.length ids)) funs
  | e -> Base.Core_util.ast_iter (iter_under f depth) e

(* The calls of each local fixpoint in [body] made where it is bound, under
   its occurrence: the fixpoint applied there, by its occurrence, or the
   reads of the let binding it. *)
let bound_calls body =
  let found = ref [] in
  let rec walk e =
    ( match e with
    | Core.Expr.Let {value = (Core.Expr.Fixpoint {occurrence; _} | Core.Expr.Cofixpoint {occurrence; _});
                     body = b; _} ->
      let reads = ref [] in
      iter_under
        (fun depth -> function Core.Expr.Bound_variable {index = k; occurrence = read} when k = depth
          + 1 -> reads := read :: !reads | _ -> ()) 0 b;
      found := (occurrence, List.rev !reads) :: !found
    | Core.Expr.Apply {callee = (Core.Expr.Fixpoint {occurrence; _} | Core.Expr.Cofixpoint {occurrence; _}); _} ->
      found := (occurrence, [occurrence]) :: !found
    | _ -> () );
    Base.Core_util.ast_iter walk e
  in
  walk body;
  !found

(* The plan of every local fixpoint in [defs], one per fixpoint, under its
   occurrence.  Inside a member's body, before its parameters,
   the member [k] of [n] is the variable [n - k]. *)
let local_groups ~suspension ~effects defs =
  let plans = ref [] in
  let plan ~bound origin lex ids funs occurrence =
    let n = Array.length ids in
    let arities = Array.map (fun f -> fst (split_params 0 f)) funs in
    let member ~within ~depth f =
      match strip f with
      | Core.Expr.Bound_variable {index = db; _} ->
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
        Core.Lexenv.push
          (List.rev_map
             (fun (g, ty) -> {Core.Lexenv.id = g; type_ = ty; role = Core.Lexenv.Value})
             (Array.to_list ids) )
          lex
      in
      Array.exists (suspends_within ~suspension ~self:origin lex) funs
    in
    let adoptable =
      List.init n (fun j ->
          let names ~depth = function
            | Core.Expr.Bound_variable _ as read -> Option.has_some (member ~within:j ~depth:(depth - arities.(j)) read)
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
              | Some k, Core.Expr.Bound_variable {occurrence = read; _} -> reads.(k) <- read :: reads.(k)
              | _ -> (
                match e with
                | Core.Expr.Apply {callee = head; _} -> (
                  match (member ~within:j ~depth head, strip head) with
                  | Some k, Core.Expr.Bound_variable {occurrence = read; _} -> calls.(k) <- read :: calls.(k)
                  | _ -> () )
                | _ -> () ) )
            0
            (snd (split_params 0 f)) )
        funs;
      (Array.to_list calls, Array.to_list reads)
    in
    let named =
      List.map2
        (fun calls reads -> List.exists (fun r -> not (List.exists (Core.Occurrence.equal r) calls)) reads) calls reads
    in
    plans :=
      { occurrence;
        local_kind = kind;
        chains;
        suspends;
        adoptable;
        calls;
        named;
        entered = List.concat_map (fun (o, calls) -> if Core.Occurrence.equal o occurrence then calls else []) bound }
      :: !plans
  in
  Core.Ref.User.Map.iter
    (fun r (fd : Core.Recursion.Definition.t) ->
      let lex, body = Elaborate.declaration_scope fd.type_ fd.body in
      let bound = bound_calls body in
      iter_scoped
        (fun lex -> function
          | Core.Expr.Fixpoint rec_group | Core.Expr.Cofixpoint rec_group ->
            let ids = Core.Recursion.Group.functions rec_group
            and funs = Core.Recursion.Group.bodies rec_group
            and occ = rec_group.occurrence in
            plan ~bound r lex ids funs occ
          | _ -> ())
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
  made_of : Core.Occurrence.t;
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
let inlined_calls ~suspension ~self ~effects ~parameters ~inlines body =
  let effect_ = sequential effects in
  let found = ref [] in
  let rec go pos e =
    let operand = go Operand in
    match e with
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when Base.Table.is_custom use.callee ->
      List.iter operand args
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when inlines use ->
      let n = List.length args and k = parameters use.callee in
      if n >= k then
        found :=
          { callee = use.callee;
            continues = n = k && (pos = Returning || pos = Returned);
            made_of = Core.Global_use.occurrence use }
          :: !found;
      List.iter operand args
    | Core.Expr.Coerce {value = a; _}
    | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} -> go pos a
    | Core.Expr.Construct {constructor = c; arguments = [a]; _} when identity c -> go pos a
    | Core.Expr.Apply {callee = Core.Expr.Global use;
                       arguments = [a]} when identity use.callee && Base.Table.to_inline use.callee -> go pos a
    | Core.Expr.Construct {result_type = Core.Type.Global_app {head = n; _}; constructor = c; arguments = args; _}
      when (not (Base.Table.is_custom c))
           && suspension.at_constructor ~self:(Some self) ~binder_type:(fun _ -> None) n args ->
      ()
    | Core.Expr.Let {binder = x; value = a; body = b; _} -> (
      match pos with
      | Operand | Returned -> ()
      | Returning | Binding ->
        if x != Core.Binder_name.Anonymous then go Binding a;
        go pos b )
    | Core.Expr.Match {scrutinee_type = ty; scrutinee = s; branches; _} -> (
      let enum =
        match ty with
        | Core.Type.Global_app {head = (Names.GlobRef.IndRef _ as r); _} -> Base.Table.is_enum_inductive r
        | _ -> false
      in
      match pos with
      | Operand | Returned -> ()
      | Binding when not (match_bound_in_place ty branches) -> ()
      | (Returning | Binding) when enum && not (Base.Table.is_custom_match branches) -> ()
      | Returning | Binding ->
        operand s;
        Array.iter (fun {Core.Match.Branch.body = b; _} -> go pos b) branches )
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Bind -> (
      match (pos, List.rev args) with
      | (Returning | Binding), Core.Expr.Lambda {body = k; _} :: action :: rest ->
        List.iter operand (List.rev rest);
        operand action;
        go pos k
      | _ -> () )
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when effect_ use = Some Effects.Return -> (
      match List.rev args with
      | value :: rest ->
        List.iter operand (List.rev rest);
        go (match pos with Returning | Returned -> Returned | Binding | Operand -> Operand) value
      | [] -> () )
    | Core.Expr.Apply {callee = (Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _); arguments = args} -> (
      match pos with Operand | Returned -> () | Returning | Binding -> List.iter operand args )
    | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ | Core.Expr.Lambda _ -> ()
    | Core.Expr.Apply {callee = f; arguments = args} ->
      operand f;
      List.iter operand args
    | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.iter operand args
    | Core.Expr.Persistent_array {elements = a; default = d} ->
      Array.iter operand a;
      operand d
    | Core.Expr.Bound_variable _
    | Core.Expr.Global _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _
    | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ -> ()
  in
  go Returning body;
  List.rev !found

(* The body of the function [r], defined as [fd], as it is generated: [None]
   where it is suspended whole. *)
let flow_of ~suspension r (fd : Core.Recursion.Definition.t) =
  let _, body = Elaborate.declaration_scope fd.type_ fd.body in
  if suspension.whole r (Base.Type_util.core_return_type fd.type_) body then None else Some body

(* The number of parameters the definition [fd] is generated taking: every
   one its type declares. *)
let definition_parameter_count (fd : Core.Recursion.Definition.t) =
  List.length (Base.Type_util.core_domains (Base.Core_util.type_simpl fd.type_))

(* The number of parameters of [g], among the definitions [defs]. *)
let parameters defs g =
  match Core.Ref.User.Map.find_opt g defs with
  | Some fd -> definition_parameter_count fd
  | None -> 0

(* The partner of [self] spliced next into [body], its body as generated,
   with the calls of it spliced ({!inlined_calls}): the partner of the first
   such call met of a function [pending] holds, whose calls are all spliced
   at once.  A call [opaque] holds is in a partner's body run in place of a
   call, where nothing is spliced. *)
let next_inlining ~suspension ~opaque ~effects ~defs ~pending self body =
  let calls ~inlines =
    let inlines (use : Core.Global_use.t) =
      inlines use.callee && not (List.exists (Core.Occurrence.equal (Core.Global_use.occurrence use)) opaque)
    in
    inlined_calls ~suspension ~self ~effects ~parameters:(parameters defs) ~inlines body
  in
  match calls ~inlines:pending with
  | [] -> None
  | {callee = partner; _} :: _ ->
    let found = calls ~inlines:(Base.Common.globref_equal partner) in
    let these continues = List.filter_map (fun c -> if c.continues = continues then Some c.made_of else None) found in
    Some {partner; continued = these true; invoked = these false}

(* Why the partners of [r] are not spliced. *)
let unspliced why r =
  Base.Probe.hit "SPLICE_declined" (fun () -> why ^ " " ^ Base.Table.kername_of_global r);
  None

(* Whether the use [use] solves one of its callee's variables to a type, or
   is written at a type other than the variable in its place: the callee's
   body is then another function there.  A use within its callee's
   recursive group is solved at the group's own variables, whatever it is
   written at -- [g bool] in [g]'s partner. *)
let solves_variables use =
  let solved =
    Option.cata
      (Core.Scheme.Instantiation.exists (fun _ (s : Core.Type.t Core.Scheme.slot) ->
           match s.solution with Core.Scheme.Type _ -> true | Core.Scheme.Identity -> false ) )
      false (Core.Global_use.instantiation use)
  in
  let written_elsewhere (v, t) =
    match Base.Core_util.type_simpl t with Core.Type.Variable {variable = i; _} -> i <> Core.Scheme.Var.ordinal v | _ -> true
  in
  solved || List.exists written_elsewhere (Core.Global_use.written_evidence use)

(* The occurrences of the global uses in [e]. *)
let uses_in e =
  let found = ref [] in
  let rec walk = function
    | Core.Expr.Global use -> found := Core.Global_use.occurrence use :: !found
    | e -> Base.Core_util.ast_iter walk e
  in
  walk e;
  !found

(* [body] with each call of the function defined as [def] made at [sites]
   replaced by [def]'s body, its parameters bound to the call's arguments
   ({!Copy.call}), and the uses in the bodies so copied; [Error why]
   unless every site is such a call, with an argument for each parameter,
   of a use that solves none of its callee's variables, whose body then
   needs no instantiation. *)
let splice_calls (def : Core.Recursion.Definition.t) sites body =
  let left = ref sites and copied = ref [] in
  let at use = List.exists (Core.Occurrence.equal (Core.Global_use.occurrence use)) !left in
  let exception Unspliced of string in
  let rec go e =
    match e with
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when at use -> (
      if solves_variables use then raise_notrace (Unspliced "instantiated");
      match Copy.call ~ty:def.type_ use def.body args with
      | None -> raise_notrace (Unspliced "arguments")
      | Some spliced ->
        left := List.filter (fun o -> not (Core.Occurrence.equal o (Core.Global_use.occurrence use))) !left;
        let passed = List.concat_map uses_in args in
        copied := List.filter (fun o -> not (List.exists (Core.Occurrence.equal o) passed)) (uses_in spliced) @ !copied;
        spliced )
    | _ -> Base.Core_util.ast_map go e
  in
  match go body with
  | body -> if !left = [] then Ok (body, !copied) else Error "unreached"
  | exception Unspliced why -> Error why

(* The effect operations of [fd]'s body alone, generated in its mode. *)
let definition_effects fd =
  Effects.analyze
    [ ( Names.ModPath.MPfile Names.DirPath.empty,
        [(Names.Label.make "spliced",
            Core.Module.Structure_item.Declaration (Core.Decl.Recursive_group (Core.Nonempty.singleton fd)))] ) ]

(* Whether functions of types [a] and [b] yield one type, once every
   abbreviation is unfolded, whatever [Type Expand] says the C++ spells, a
   variable of the definition's scheme read alike whether it is written as
   the scheme's or, under a binder inside it, as rigid. *)
let yields_alike a b =
  let rec unfold = function
    | Core.Type.Meta {contents = Some t} -> unfold t
    | Core.Type.Global_app {head = (Names.GlobRef.ConstRef kn as r); type_arguments = args; index_arguments = a} -> (
      match Base.Table.lookup_typedef_unchecked kn with
      | Some t -> unfold (Base.Core_util.type_subst_list args t)
      | None -> Core.Type.Global_app {head = r; type_arguments = List.map unfold args; index_arguments = a} )
    | Core.Type.Global_app {head = r; type_arguments = args; index_arguments = a} ->
      Core.Type.Global_app {head = r; type_arguments = List.map unfold args; index_arguments = a}
    | Core.Type.Variable_app {head = i; arguments = args} ->
      Core.Type.Variable_app {head = i; arguments = List.map unfold args}
    | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = unfold a; result = unfold b}
    | t -> t
  in
  let returns ty = Base.Core_util.rigidify (unfold (Base.Type_util.core_return_type (Base.Core_util.type_simpl ty))) in
  Base.Core_util.eq_core_type (returns a) (returns b)

(* The calls of [g] the partner [def] makes where its body runs in place of
   a call of it ({!inlined_calls}), and the number of its uses of [g] there
   in all. *)
let flow_calls ~suspension ~defs (def : Core.Recursion.Definition.t) g =
  match flow_of ~suspension def.entity def with
  | None -> ([], 0)
  | Some body ->
    let of_g (use : Core.Global_use.t) = Base.Common.globref_equal use.callee g in
    let uses = ref 0 in
    let rec count = function Core.Expr.Global use when of_g use -> incr uses | e -> Base.Core_util.ast_iter count e in
    count body;
    ( inlined_calls ~suspension ~self:def.entity ~effects:(definition_effects def) ~parameters:(parameters defs)
        ~inlines:of_g
        body,
      !uses )

(* The calls of [self] the partner [def] makes where its body runs in place
   of a call of it. *)
let calls_back ~suspension ~defs ~self def = fst (flow_calls ~suspension ~defs def self)

(* Whether each use the partner [def] makes of itself is a call where its
   body runs: the copy a machine enters is no value, so a use in a closure,
   a partial application or anything run in a lambda would have nothing to
   call. *)
let calls_itself_in_flow ~suspension ~defs (def : Core.Recursion.Definition.t) =
  let calls, uses = flow_calls ~suspension ~defs def def.entity in
  List.length calls = uses

(* [body], the body of a function, with each call of its partner defined as
   [def] made at [sites] replaced by a call of a copy of the partner bound in
   front of it, and the occurrence of the copy: a local fixpoint whose calls
   of the partner are its own, so that the machine entering it where the
   calls were runs every turn of the partner as one of its own.  [Error why]
   unless every site is such a call, with an argument for each of the
   partner's parameters, of a use that solves none of its variables, as is
   every call of the partner its body makes. *)
let adopt_calls (def : Core.Recursion.Definition.t) sites body =
  let partner = def.entity in
  let arity = List.length (Base.Type_util.core_domains (Base.Core_util.type_simpl def.type_)) in
  let left = ref sites in
  let at use = List.exists (Core.Occurrence.equal (Core.Global_use.occurrence use)) !left in
  let exception Unspliced of string in
  let instance use = if solves_variables use then raise_notrace (Unspliced "instantiated") in
  let rec own depth = function
    | Core.Expr.Global (use : Core.Global_use.t) when Names.GlobRef.UserOrd.equal use.callee partner ->
      instance use;
      Core.Expr.Bound_variable {index = depth + 1; occurrence = Core.Occurrence.fresh ()}
    | e -> Base.Core_util.ast_map_lift own depth e
  in
  let rec reroute depth e =
    match e with
    | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} when at use ->
      instance use;
      if List.length args <> arity then raise_notrace (Unspliced "arguments");
      left := List.filter (fun o -> not (Core.Occurrence.equal o (Core.Global_use.occurrence use))) !left;
      Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = depth + 1; occurrence = Core.Occurrence.fresh ()};
                       arguments = List.map (reroute depth) args}
    | _ -> Base.Core_util.ast_map_lift reroute depth e
  in
  let params, inner = Base.Core_util.collect_lams body in
  match (own 0 (Copy.copy def.body), reroute 0 (Base.Core_util.ast_lift 1 inner)) with
  | _ when arity = 0 -> Error "arguments"
  | _ when !left <> [] -> Error "unreached"
  | copy, inner ->
    let name = Names.Id.of_string (Names.Id.to_string (Base.Table.safe_basename_of_global partner) ^ "_entry") in
    let entered = Core.Occurrence.fresh () in
    let fixpoint =
      Core.Expr.Fixpoint (Core.Recursion.Group.of_arrays ~selected:0 ([|(name, def.type_)|]) ([|copy|]) entered) in
    Ok (Base.Core_util.named_lams params (Core.Expr.Let {binder = Core.Binder_name.Source name;
                                                 binder_type = def.type_;
                                                 value = fixpoint;
                                                 body = inner;
                                                 occurrence = Core.Occurrence.fresh ()}), entered)
  | exception Unspliced why -> Error why

(* Whether the function defined as [fd] calls itself once its partners are
   spliced into it: only a function that does is lowered as a loop. *)
let recurses (fd : Core.Recursion.Definition.t) =
  let arity = List.length (Base.Type_util.core_domains (Base.Core_util.type_simpl fd.type_)) in
  let callee ~depth:_ = function
    | Core.Expr.Global (use : Core.Global_use.t) when Names.GlobRef.UserOrd.equal use.callee fd.entity -> Some arity
    | _ -> None
  in
  let _, body = Elaborate.declaration_scope fd.type_ fd.body in
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
let splice_member ~suspension ~inlines ~defs ~members (fd : Core.Recursion.Definition.t) =
  let self = fd.entity in
  let own_vars = Base.Core_util.type_maxvar fd.type_ in
  let own_monad = Base.Type_util.codomain_monad fd.type_ in
  let partner g = (not (Base.Common.globref_equal g self)) && List.exists (Base.Common.globref_equal g) members in
  let enterable (def : Core.Recursion.Definition.t) =
    inlines self && yields_alike fd.type_ def.type_ && calls_back ~suspension ~defs ~self def <> []
    && calls_itself_in_flow ~suspension ~defs def
    && not (definition_suspends ~suspension self fd.type_ fd.body)
  in
  let rec go opaque inlined entered body =
    let current = {fd with Core.Recursion.Definition.body = body} in
    let flow = flow_of ~suspension self current in
    let next pending =
      Option.bind flow (next_inlining ~suspension ~opaque ~effects:(definition_effects current) ~defs ~pending self)
    in
    let spliced g = List.exists (Base.Common.globref_equal g) inlined in
    let finished = Some (List.rev inlined, entered, body) in
    match next (fun g -> partner g && not (spliced g)) with
    | None -> (
      match next spliced with
      | Some {partner; continued = []; invoked = _ :: _ as invoked} when entered = None -> (
        let def = Core.Ref.User.Map.find partner defs in
        if not (enterable def) then finished
        else
          match adopt_calls def invoked body with
          | Ok (body, o) -> go opaque inlined (Some o) body
          | Error _ -> finished )
      | Some _ | None -> finished )
    | Some {partner; continued; invoked} -> (
      let def = Core.Ref.User.Map.find partner defs in
      if Base.Core_util.type_maxvar def.type_ <> own_vars then unspliced "variables" self
      else if not (Option.equal Names.GlobRef.UserOrd.equal (Base.Type_util.codomain_monad def.type_) own_monad) then
        unspliced "monad" self
      else if Option.is_empty (flow_of ~suspension partner (Core.Ref.User.Map.find partner defs)) then
        unspliced "suspended" self
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
  match go [] [] None fd.body with
  | Some ((_ :: _), _, body) when not (recurses {fd with Core.Recursion.Definition.body = body}) ->
    Some ([], None, fd.body)
  | spliced -> spliced

let splice_partners ~suspension ~loopified ~inlines ({structure = struc;
                                          splices} : Core_passes.Phase.normalizing) : Core_passes.Phase.normalizing =
  let groups = Recursive_groups.analyze struc in
  let originals = ref Core.Ref.User.Map.empty in
  Core_passes.Modutil.struct_iter
    (fun d ->
      List.iter (fun (fd : Core.Recursion.Definition.t) -> originals := Core.Ref.User.Map.add fd.entity fd !originals)
        (Base.Core_util.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let defs = !originals in
  let splicings =
    Core.Ref.User.Map.filter_map
      (fun r fd ->
        match Recursive_groups.group groups r with
        | Some members when loopified r && (not (Base.Table.is_custom r)) && not (Core_passes.Splices.decided splices r) ->
          Some (splice_member ~suspension ~inlines ~defs ~members fd)
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
      (fun m -> match Core.Ref.User.Map.find_opt m splicings with Some None -> true | Some (Some _) | None -> false)
      (Option.default [] (Recursive_groups.group groups r))
  in
  (* Each member decided: the copy its machine enters, if any, and its
     spliced body, if it changes. *)
  let decision r = function
    | Some (_ :: _, _, _) when declined r -> unspliced "group" r
    | Some (_ :: _, entered, body) ->
      Base.Probe.hit "SPLICE_spliced" (fun () -> Base.Table.kername_of_global r);
      Some (entered, Some body)
    | Some ([], _, _) -> Some (None, None)
    | None -> None
  in
  let decisions = Core.Ref.User.Map.filter_map decision splicings in
  let splice (fd : Core.Recursion.Definition.t) =
    match Core.Ref.User.Map.find_opt fd.entity decisions with
    | Some (_, Some body) -> {fd with Core.Recursion.Definition.body = body}
    | Some (_, None) | None -> fd
  in
  { structure =
      Core_passes.Modutil.map_struct_decls
        (function
          | Core.Decl.Recursive_group fds -> Core.Decl.Recursive_group (Core.Nonempty.map splice fds)
          | Core.Decl.Value {entity = r; body = b; type_ = ty} ->
            let fd = splice {Core.Recursion.Definition.entity = r; body = b; type_ = ty} in
            Core.Decl.Value {entity = r; body = fd.body; type_ = ty}
          | d -> d )
        struc;
    splices = Core.Ref.User.Map.fold (fun r (entered, _) s -> Core_passes.Splices.decide ?entered r s) decisions splices }

(* A member of a group recurses by the calls of itself it makes, those in
   the copies of its partners spliced into its body included
   ({!splice_partners}), and only those: a partner's call that was not
   spliced stays a call of another function.  A function on no cycle calls
   no function it could recurse through. *)
let analyze ~suspension groups program =
  let struc = Core_passes.Phase.structure program in
  let effects = Effects.analyze struc in
  let defs = ref Core.Ref.User.Map.empty in
  let add (fd : Core.Recursion.Definition.t) = defs := Core.Ref.User.Map.add fd.entity fd !defs in
  Core_passes.Modutil.struct_iter
    (fun d -> List.iter add (Base.Core_util.term_defs d))
    (fun _ -> ())
    (fun _ -> ())
    struc;
  let defs = !defs in
  (* A function is generated taking every parameter its type declares, its
     body applied to those it does not bind ({!Elaborate.declaration_scope}):
     its calls are read there, a call with fewer arguments than that being
     the closure the C++ makes of it. *)
  (* A member's own calls: what a loop of the member can take. *)
  let member_kind r (fd : Core.Recursion.Definition.t) =
    let callee ~depth:_ = function
      | Core.Expr.Global (use : Core.Global_use.t) when Names.GlobRef.UserOrd.equal use.callee r ->
        Some (definition_parameter_count fd)
      | _ -> None
    in
    classify ~effects ~callee (snd (Elaborate.declaration_scope fd.type_ fd.body))
  in
  let kinds = Core.Ref.User.Map.mapi member_kind defs in
  let plans =
    List.map
      (fun members ->
        let kind m = Option.default No_recursion (Core.Ref.User.Map.find_opt m kinds) in
        {members; kind = List.fold_left (fun k m -> combine k (kind m)) No_recursion members} )
      (Recursive_groups.groups groups)
  in
  let by_member =
    List.fold_left
      (fun m g -> List.fold_left (fun m r -> Core.Ref.User.Map.add r g m) m g.members)
      Core.Ref.User.Map.empty plans
  in
  let defined = Core.Ref.User.Map.fold (fun r _ s -> Core.Ref.User.Set.add r s) defs Core.Ref.User.Set.empty in
  (* Every recursive group has exactly one plan, and a function on no cycle
     reads as not recursing. *)
  if Base.Probe.checking () then
    Core.Ref.User.Map.iter
      (fun r _ ->
        let planned = Option.map (fun g -> g.members) (Core.Ref.User.Map.find_opt r by_member) in
        let grouped = Recursive_groups.group groups r in
        let off_cycle_recurses () = Core.Ref.User.Map.find r kinds <> No_recursion in
        if (not (Option.equal (List.equal Base.Common.globref_equal) planned grouped))
           || (grouped = None && off_cycle_recurses ())
        then
          Base.Probe.violation "recursion plan"
            Pp.(str "no single plan for the group of " ++ str (Base.Table.kername_of_global r)) )
      defs;
  let modulo_cons =
    Core.Ref.User.Map.fold
      (fun r (fd : Core.Recursion.Definition.t) m ->
        let member ~within:_ ~depth:_ = function
          | Core.Expr.Global (use : Core.Global_use.t) when Names.GlobRef.UserOrd.equal use.callee r -> Some 0
          | _ -> None
        in
        match Core.Ref.User.Map.find_opt r kinds with
        | Some Nontail -> (
          match modulo_cons_chains ~effects ~member ~bodies:[|fd.body|] 0 with
          | Some chains -> Core.Ref.User.Map.add r chains m
          | None -> m )
        | Some (Tail | No_recursion) | None -> m )
      defs Core.Ref.User.Map.empty
  in
  let suspended =
    Core.Ref.User.Map.fold
      (fun r (fd : Core.Recursion.Definition.t) s ->
        if definition_suspends ~suspension r fd.type_ fd.body then Core.Ref.User.Set.add r s else s )
      defs Core.Ref.User.Set.empty
  in
  (* A definition off every group that does not recurse only by tail calls
     resumes nowhere but in its local fixpoints. *)
  let resumes =
    Core.Ref.User.Map.mapi
      (fun r (fd : Core.Recursion.Definition.t) ->
        let members =
          match Core.Ref.User.Map.find_opt r by_member with
          | Some g when g.kind = Nontail -> g.members
          | Some _ | None -> []
        in
        (* A call with fewer arguments than its callee's parameters is a
           closure the C++ makes, whose call runs where the closure does. *)
        let rec targets = function
          | Core.Expr.Coerce {value = e; _}
          | Core.Expr.Boxed_value {value = e; _}
          | Core.Expr.Lambda_group_barrier {value = e; _} -> targets e
          | Core.Expr.Apply {callee = Core.Expr.Global (use : Core.Global_use.t); arguments = args}
            when List.exists (Base.Common.globref_equal use.callee) members
                 && List.length args >= parameters defs use.callee ->
            [{target = Function use.callee; occurrence = Core.Global_use.occurrence use}]
          | _ -> []
        in
        let lex, body = Elaborate.declaration_scope fd.type_ fd.body in
        resumes_of ~effects ~entered:(Core_passes.Splices.is_entered_copy (Core_passes.Phase.splices program))
          ~origin:r ~targets lex body )
      defs
  in
  let adoptable =
    Core.Ref.User.Map.mapi
      (fun r (fd : Core.Recursion.Definition.t) ->
        let members = match Core.Ref.User.Map.find_opt r by_member with Some g -> g.members | None -> [] in
        let names ~depth:_ = function
          | Core.Expr.Global (use : Core.Global_use.t) -> List.exists (Base.Common.globref_equal use.callee) members
          | _ -> false
        in
        let lex, body = Elaborate.declaration_scope fd.type_ fd.body in
        flow_fixpoints ~names (Core.Lexenv.depth lex) body )
      defs
  in
  let calls =
    List.fold_left
      (fun m g ->
        let uses = ref [] in
        let rec walk = function
          | Core.Expr.Global (use : Core.Global_use.t) when List.exists (Base.Common.globref_equal use.callee) g.members ->
            uses := (use.callee, Core.Global_use.occurrence use) :: !uses
          | e -> Base.Core_util.ast_iter walk e
        in
        List.iter
          (fun r -> Option.iter (fun (fd : Core.Recursion.Definition.t) -> walk fd.body) (Core.Ref.User.Map.find_opt r defs))
            g.members;
        List.fold_left
          (fun m r ->
            Core.Ref.User.Map.add r
              (List.rev (List.filter_map (fun (c, o) -> if Base.Common.globref_equal c r then Some o else None) !uses))
              m )
          m g.members )
      Core.Ref.User.Map.empty plans
  in
  { groups = plans;
    by_member;
    defined;
    locals = local_groups ~suspension ~effects defs;
    modulo_cons;
    suspended;
    resumes;
    adoptable;
    kinds;
    calls;
    let_lambdas =
      Core.Ref.User.Map.fold
        (fun _ (fd : Core.Recursion.Definition.t) found ->
          let found = ref found in
          let rec walk e =
            ( match e with Core.Expr.Let {value = Core.Expr.Lambda _;
                                          occurrence = occ; _} -> found := occ :: !found | _ -> () );
            Base.Core_util.ast_iter walk e
          in
          walk fd.body;
          !found )
        defs [] }

let same_cell c c' = Base.Common.globref_equal c.constructor c'.constructor && c.hole = c'.hole

let same_chains =
  List.equal (fun c c' ->
      List.equal same_cell c.around c'.around && same_cell c.innermost c'.innermost )

let same_target t t' =
  match (t, t') with
  | Function g, Function g' -> Base.Common.globref_equal g g'
  | Member (o, m), Member (o', m') -> Core.Occurrence.equal o o' && Int.equal m m'
  | Entering o, Entering o' -> Core.Occurrence.equal o o'
  | (Function _ | Member _ | Entering _), _ -> false

let same_call c c' = same_target c.target c'.target && Core.Occurrence.equal c.occurrence c'.occurrence

let equal a b =
  List.equal
    (fun g g' -> List.equal Base.Common.globref_equal g.members g'.members && g.kind = g'.kind)
    a.groups b.groups
  && Core.Ref.User.Set.equal a.defined b.defined
  && List.equal
       (fun (l : local_group) (l' : local_group) ->
         Core.Occurrence.equal l.occurrence l'.occurrence
         && l.local_kind = l'.local_kind
         && List.equal (Option.equal same_chains) l.chains l'.chains
         && l.suspends = l'.suspends
         && List.equal (List.equal Core.Occurrence.equal) l.adoptable l'.adoptable
         && List.equal (List.equal Core.Occurrence.equal) l.calls l'.calls
         && List.equal Bool.equal l.named l'.named
         && List.equal Core.Occurrence.equal l.entered l'.entered )
       a.locals b.locals
  && Core.Ref.User.Map.equal same_chains a.modulo_cons b.modulo_cons
  && Core.Ref.User.Set.equal a.suspended b.suspended
  && Core.Ref.User.Map.equal
       (List.equal (fun r r' ->
            Core.Binder.equal r.binder r'.binder
            && Core.Binder.same_site r.binder r'.binder
            && List.equal Core.Binder.equal r.live r'.live
            && List.equal same_call r.after r'.after
            && List.equal
                 (fun p p' ->
                   Core.Binder.equal p.passed p'.passed && Core.Binder.equal p.into p'.into
                     && same_call p.call p'.call )
                 r.passes r'.passes
            && List.equal Core.Binder.equal r.read_by_call r'.read_by_call
            && List.equal
                 (fun c c' -> Core.Binder.equal c.recomputed c'.recomputed
                   && List.equal Core.Binder.equal c.from c'.from)
                 r.recomputable r'.recomputable ) )
       a.resumes b.resumes
  && Core.Ref.User.Map.equal (List.equal Core.Occurrence.equal) a.adoptable b.adoptable
  && Core.Ref.User.Map.equal ( = ) a.kinds b.kinds
  && Core.Ref.User.Map.equal (List.equal Core.Occurrence.equal) a.calls b.calls
  && List.equal Core.Occurrence.equal a.let_lambdas b.let_lambdas

(* Whether some member of the group of [r] suspends. *)
let suspends t r =
  let members = match Core.Ref.User.Map.find_opt r t.by_member with Some g -> g.members | None -> [r] in
  List.exists (fun m -> Core.Ref.User.Set.mem m t.suspended) members

let tail_loops t =
  let functions =
    Core.Ref.User.Map.fold (fun r kind acc -> if kind = Tail && not (suspends t r) then r :: acc else acc) t.kinds []
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
    Core.Ref.User.Map.fold
      (fun r kind acc ->
        if kind = Nontail && (not (suspends t r)) && not (Core.Ref.User.Map.mem r t.modulo_cons) then r :: acc else acc )
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
  let functions = Core.Ref.User.Map.fold (fun r _ acc -> if suspends t r then acc else r :: acc) t.modulo_cons [] in
  let locals =
    List.filter_map
      (fun (l : local_group) ->
        match l.chains with
        | [Some (_ :: _)] when l.local_kind = Nontail && not l.suspends -> Some l.occurrence
        | _ -> None )
      t.locals
  in
  (List.rev functions, locals)

let group_of t r = Core.Ref.User.Map.find_opt r t.by_member

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
let strategy t ~pointer_fields r =
  if Core.Ref.User.Set.mem r t.defined then
    let kind = Option.default No_recursion (Core.Ref.User.Map.find_opt r t.kinds) in
    let members = match group_of t r with Some g -> g.members | None -> [r] in
    let suspends = List.exists (fun m -> Core.Ref.User.Set.mem m t.suspended) members in
    Some
      (strategy_of ~pointer_fields ~suspends kind (Core.Ref.User.Map.find_opt r t.modulo_cons))
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
let strategy_at t ~pointer_fields (occurrence, member) =
  List.fold_left
    (fun found (l : local_group) ->
      if Core.Occurrence.equal l.occurrence occurrence then
        match List.nth_opt l.chains member with
        | Some chains ->
          let this = strategy_of ~pointer_fields ~suspends:l.suspends l.local_kind chains in
          Some (match found with Some f -> both f this | None -> this)
        | None -> found
      else found )
    None t.locals

let adoptable_in t r = Option.default [] (Core.Ref.User.Map.find_opt r t.adoptable)

(* Copies of a fixpoint share its occurrence, and plan alike. *)
let adoptable_at t (occurrence, member) =
  List.find_map
    (fun (l : local_group) ->
      if Core.Occurrence.equal l.occurrence occurrence then List.nth_opt l.adoptable member else None )
    t.locals
  |> Option.default []

let adoptable_by_fixpoint t ~lifted occurrence =
  List.exists
    (fun (l : local_group) ->
      List.exists (Core.Occurrence.equal l.occurrence) lifted
      && List.exists (List.exists (Core.Occurrence.equal occurrence)) l.adoptable )
    t.locals

let adoptable_somewhere t ~lifted occurrence =
  Core.Ref.User.Map.exists (fun _ os -> List.exists (Core.Occurrence.equal occurrence) os) t.adoptable
  || adoptable_by_fixpoint t ~lifted occurrence

let calls t r = Option.default [] (Core.Ref.User.Map.find_opt r t.calls)

(* Copies of a fixpoint share its occurrence, and so do their calls. *)
let member_calls t (occurrence, member) =
  List.concat_map
    (fun (l : local_group) ->
      if Core.Occurrence.equal l.occurrence occurrence then Option.default [] (List.nth_opt l.calls member)
      else [] )
    t.locals

let named_as_value t (occurrence, member) =
  List.exists
    (fun (l : local_group) -> Core.Occurrence.equal l.occurrence occurrence && List.nth_opt l.named member = Some true)
    t.locals

let entering t occurrence =
  member_calls t (occurrence, 0)
  @ List.concat_map
      (fun (l : local_group) -> if Core.Occurrence.equal l.occurrence occurrence then l.entered else [])
      t.locals

let resumes_binding t (b : Core.Binder.t) =
  match Core.Ref.User.Map.find_opt b.origin t.resumes with
  | Some rs -> List.filter (fun r -> Core.Binder.equal r.binder b && Core.Binder.same_site r.binder b) rs
  | None -> []

(* A lambda a let binds does not call itself. *)
let strategy_of_let t occurrence =
  if List.exists (Core.Occurrence.equal occurrence) t.let_lambdas then Some No_loop else None
