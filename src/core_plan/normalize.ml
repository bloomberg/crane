(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

(* The placeholder for the [i]th call taken out of a scope, replaced once the
   binder it is read through is known. *)
let marker = "\000normalize:"

let placeholder i = Core.Expr.Runtime_error (marker ^ string_of_int i)

let placeholder_index = function
  | Core.Expr.Runtime_error s when String.starts_with ~prefix:marker s ->
    int_of_string_opt (String.sub s (String.length marker) (String.length s - String.length marker))
  | _ -> None

(* [replace_placeholders f e]: each placeholder [i] in [e] becomes [f i].
   Placeholders sit only at strictly evaluated positions of the scope they
   were made in, never under a binder, so no index needs adjusting. *)
let rec replace_placeholders f e =
  match placeholder_index e with
  | Some i -> f i
  | None -> Base.Core_util.ast_map (replace_placeholders f) e

(* A local fixpoint function: its declared type, and its arity, the
   lambdas its body starts with.  The type may leave its result open; the
   arity is what says a call is a full one. *)
type local = {type_ : Core.Type.t; arity : int}

(* The functions whose calls are bound: a top-level fixpoint group, by
   reference, and the local fixpoints enclosing the term, each by the depth
   its bodies start at and its functions, the [j]th being [Core.Expr.Bound_variable (j + 1)]
   there.  [own_tvars] counts the type variables of the declaration, [Core.Type.Variable 1]
   to [Core.Type.Variable own_tvars]; [fresh] names the next temporary of the declaration,
   [effects] are the effect operations of the program it is in, and
   [splices] what splicing decided there ({!Recursion.splice_partners}). *)
type group = {
  globals : GlobRef.t list;
  own_tvars : int;
  locals : (int * local array) list;
  fresh : unit -> Core.Binder_name.t;
  effects : Effects.t;
  splices : Core_passes.Splices.t;
}

(* A supply of the declaration's temporaries, numbered from 1, so no two of
   its bindings share a name, whichever branches they sit in. *)
let temporaries () =
  let n = ref 0 in
  fun () ->
    incr n;
    Core.Binder_name.Generated (Base.Core_util.temporary_id !n)

(* A full application yields what its function's type ends in.  A partial
   one yields a function: there is nothing to evaluate early, and naming it
   would turn a direct argument into a closure. *)
let full_result = function Some (Core.Type.Arrow _) -> None | ty -> ty

type lowering = {
  app_result_type : Core.Expr.t -> Core.Expr.t list -> Core.Type.t option;
  return_type_is_erased : Id.t list -> Core.Type.t -> bool;
  suspension : Recursion.suspension;
}

(* The type a call at binder depth [depth] to one of [group]'s functions
   yields, if it is one and is applied fully. *)
let group_call cx group ~depth e =
  match e with
  | Core.Expr.Apply {callee = (Core.Expr.Global {callee = r; _} as f);
                     arguments = args} when List.exists (GlobRef.UserOrd.equal r) group.globals ->
    full_result (cx.app_result_type f args)
  | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = k; _}; arguments = args} -> (
    match
      List.find_map
        (fun (root, fns) ->
          let j = k - (depth - root) - 1 in
          if j >= 0 && j < Array.length fns then Some fns.(j) else None )
        group.locals
    with
    | Some l when List.length args = l.arity ->
      let value_args = List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args in
      (* What it yields, or, where the fixpoint's type does not say, an open
         annotation of the temporary's own: the program is frozen. *)
      Some
        (Option.default (Base.Core_util.new_open ())
           (Base.Type_util.core_codomain_after (List.length value_args) l.type_))
    | _ -> None )
  | _ -> None

(* How the value of a call is read where it stands: through a coercion
   into a type, as a field of the constructor it is an argument of, or
   passed on as it is to anything else. *)
type reading =
  | Coerced of Core.Type.t
  | Stored
  | Passed

(* The type the temporary binding the call [e], of type [ty], read as
   [reading] says, is declared at, or [None] where the call is left in
   place.  A function whose result is a type index
   ({!Base.Type_util.result_is_index_only_tvar}: [eval : expr A -> A]) returns
   it boxed, and a temporary at [ty] holds it unboxed, cast where it is
   bound.  Where [ty] names a type variable the declaration does not bind
   -- one a constructor hides, the [A * B] of [fst (eval p)] or the
   components of the pair [(eval x, eval y)] -- no C++ type spells it, and
   only the box holds the value: an open annotation, which prints as the
   box.  Translation opens a boxed temporary where a coercion reads it into
   a type with a shape, and keeps it boxed where it is read at the
   function's own result type, as the pair's fields read its components.
   Coerced into a type variable, or passed on to anything else, it could be
   opened at a type of no value there, so such a call is left in place. *)
let held group ~reading e ty =
  let boxed_only =
    Base.Core_util.type_maxvar ty > group.own_tvars
    &&
    match e with
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; _} ->
      Option.cata Base.Type_util.result_is_index_only_tvar false (Query.find_type_opt r)
    | _ -> false
  in
  if not boxed_only then Some ty
  else
    match reading with
    | Stored -> Some (Base.Core_util.new_open ())
    | Coerced into -> (
      match Base.Core_util.type_simpl into with
      | Core.Type.Variable _ | Core.Type.Variable_app _ -> None
      | _ -> Some (Base.Core_util.new_open ()) )
    | Passed -> None

(* Whether [e], at binder depth [depth], calls one of [group]'s functions
   where it is evaluated with [e]: under a branch or a let body, but not
   under a lambda -- except a local fixpoint applied there and then, whose
   body runs with it. *)
let rec reaches_call cx group ~depth e =
  group_call cx group ~depth e <> None
  ||
  match e with
  | Core.Expr.Apply {callee = Core.Expr.Fixpoint rec_group; arguments = args} ->
    let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
    List.exists (reaches_call cx group ~depth) args || fix_reaches_call cx group ~depth ids bodies
  | Core.Expr.Lambda _ | Core.Expr.Fixpoint _ | Core.Expr.Cofixpoint _ -> false
  | Core.Expr.Let {value = rhs; body; _} ->
    reaches_call cx group ~depth rhs || reaches_call cx group ~depth:(depth + 1) body
  | Core.Expr.Match {scrutinee = scrut; branches; _} ->
    reaches_call cx group ~depth scrut || branch_reaches_call cx group ~depth branches
  | Core.Expr.Apply {callee = f; arguments = args} -> List.exists (reaches_call cx group ~depth) (f :: args)
  | Core.Expr.Construct {arguments = args; _} | Core.Expr.Tuple args -> List.exists (reaches_call cx group ~depth) args
  | Core.Expr.Coerce {value = e; _}
  | Core.Expr.Boxed_value {value = e; _}
  | Core.Expr.Lambda_group_barrier {value = e; _} ->
    reaches_call cx group ~depth e
  | _ -> false

(* Whether a local fixpoint's bodies, below their parameters, reach [group]. *)
and fix_reaches_call cx group ~depth ids bodies =
  let rec params depth = function Core.Expr.Lambda {body = b; _} -> params (depth + 1) b | b -> (depth, b) in
  Array.exists
    (fun b ->
      let depth, b = params (depth + Array.length ids) b in
      reaches_call cx group ~depth b )
    bodies

and branch_reaches_call cx group ~depth branches =
  Array.exists
    (fun {Core.Match.Branch.binders = ids; body = b; _} -> reaches_call cx group ~depth:(depth + List.length ids) b)
    branches

(* How many nodes copying what follows a bound match into its branches may
   add ({!scope}).  Each copy is what follows one match, never the program
   around it, so code grows by at most this much per match, however the
   matches nest.  Every match the corpus binds this way has fewer than ten
   nodes after it, in at most four branches. *)
let duplication_budget = 32

(* [e], a term under one binder, under [n] more between that binder and the
   ones around [e]. *)
let below_first n e = Base.Core_util.permut_rels n 1 (Base.Core_util.ast_lift n e)

(* [e] with each temporary it binds renamed by [fresh]: a copy of a term
   binding temporaries binds temporaries of its own. *)
let rec renamed_temporaries fresh e =
  match e with
  | Core.Expr.Let {binder = Core.Binder_name.Generated x;
                   binder_type = ty;
                   value = a;
                   body = b;
                   occurrence = occ} when Base.Core_util.is_temporary_id x ->
    Core.Expr.Let {binder = fresh ();
                   binder_type = ty;
                   value = renamed_temporaries fresh a;
                   body = renamed_temporaries fresh b;
                   occurrence = occ}
  | _ -> Base.Core_util.ast_map (renamed_temporaries fresh) e

let into_branches ~fresh ~rty (id, ty, occ) branches rest =
  if (Array.length branches - 1) * Base.Core_util.ast_size rest > duplication_budget then None
  else
    let renamed = function Core.Binder_name.Generated x when Base.Core_util.is_temporary_id x -> fresh () | id -> id in
    let branch i ({Core.Match.Branch.binders = ids; body = b; _} as br) =
      let id, rest, occ =
        if i = 0 then (id, rest, occ)
        else (renamed id, renamed_temporaries fresh (Copy.copy rest), Core.Occurrence.fresh ())
      in
      let n = List.length ids in
      let rec plug m = function
        | Core.Expr.Let {binder = x; binder_type = tx; value = a; body = b; occurrence = o} ->
          Core.Expr.Let {binder = x; binder_type = tx; value = a; body = plug (m + 1) b; occurrence = o}
        | b ->
          Core.Expr.Let {binder = id; binder_type = ty; value = b; body = below_first (n + m) rest; occurrence = occ}
      in
      {br with Core.Match.Branch.result_type = rty; body = plug 0 b}
    in
    Some (Array.mapi branch branches)

(* [scope ~group ~depth ?expected e] -- [e], at binder depth [depth], with
   every call to [group] that sits at a strictly evaluated, non-tail
   position bound to a variable first, in evaluation order.  Branches,
   lambda bodies, let bodies, a bind's arguments and a coinductive
   constructor's are scopes of their own.  A coercion is no scope: a call it
   reads is bound like any other, [S (eval x)] becoming
   [let t := eval x in S t], with the coercion kept around the temporary
   ({!held}).  Tail modulo cons sees through the bindings
   ({!Cpp_passes.Temporaries} restores the expression before it looks), so a
   constructor's arguments are bound like any other.

   A match bound to a variable runs where it is bound, in a lambda invoked
   in place or a conditional expression, so the calls ending its branches
   are no turns of a loop ({!Recursion.match_bound_in_place}).  Where
   the scope's type is known ([expected], a branch's annotation), what
   follows such a match is copied into each of its branches instead, after
   the branch's own bindings: [let t := match x with p => b in k] becomes
   [match x with p => let t := b in k], evaluated in the same order, as
   long as the copies stay within {!duplication_budget}. *)
let rec scope cx ~group ~depth ?expected e =
  let group_call = group_call cx group ~depth in
  let inner ?(group = group) ?expected binders = scope cx ~group ~depth:(depth + binders) ?expected in
  let taken = ref [] in
  let count = ref 0 in
  let take call ty =
    incr count;
    taken := (call, ty) :: !taken;
    placeholder !count
  in
  let enters_group = function
    | Core.Expr.Fixpoint rec_group ->
      let ids = Core.Recursion.Group.functions rec_group and bodies = Core.Recursion.Group.bodies rec_group in
      fix_reaches_call cx group ~depth ids bodies
    | _ -> false
  in
  let rec strict ?(reading = Passed) ~tail e =
    match e with
    | Core.Expr.Apply {callee = (Core.Expr.Global use as f); arguments = args}
      when Effects.lookup group.effects use = Some {operation = Bind; mode = Sequential} ->
      (* Monadic sequencing: the action runs where the bind puts it, and a
         recursive call that is the whole action is a tail call there.  A
         reified bind is a call building the tree, its action evaluated
         first, like any other call's argument. *)
      Core.Expr.Apply {callee = f; arguments = List.map (inner 0) args}
    | Core.Expr.Apply {callee = f; arguments = args} -> (
      let e' = Core.Expr.Apply {callee = strict ~tail:false f; arguments = List.map (strict ~tail:false) args} in
      match group_call e', f with
      | Some ty, _ when not tail -> Option.cata (take e') e' (held group ~reading e' ty)
      | None, Core.Expr.Fixpoint g when (not tail) && enters_group f ->
        (* A local fixpoint applied here that recurses into the group is a
           call into it. *)
        let value_args = List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args in
        take e'
          (Option.default (Base.Core_util.new_open ())
             (Base.Type_util.core_codomain_after (List.length value_args) (Core.Recursion.Group.selected_member g).type_))
      | _ -> e' )
    | Core.Expr.Construct {result_type = ty;
                           constructor = (GlobRef.ConstructRef (ind, _) as r);
                           arguments = args;
                           occurrence = occ}
      when Base.Table.is_coinductive (GlobRef.IndRef ind) ->
      (* A coinductive constructor suspends its arguments. *)
      Core.Expr.Construct {result_type = ty; constructor = r; arguments = List.map (inner 0) args; occurrence = occ}
    | Core.Expr.Construct {result_type = ty;
                           constructor = r;
                           arguments = args;
                           occurrence = occ} when not (Base.Table.is_custom r) ->
      Core.Expr.Construct {result_type = ty;
                           constructor = r;
                           arguments = List.map (strict ~reading:Stored ~tail:false) args;
                           occurrence = occ}
    | Core.Expr.Construct {result_type = ty; constructor = r; arguments = args; occurrence = occ} ->
      (* A constructor mapped to custom code is what its replacement text
         makes of its arguments.  One that is just an argument ([%a0])
         stands for it, tail position included; any other ([%a0 + 1]) is an
         ordinary call. *)
      let through = Option.bind (Base.Table.find_custom_opt r) Cpp_ir.Foreign_template.passes_through in
      Core.Expr.Construct {result_type = ty; constructor = r; arguments = List.mapi
            (fun i a ->
              if through = Some i then strict ~reading ~tail a else strict ~reading:Stored ~tail:false a )
            args; occurrence = occ}
    | Core.Expr.Tuple args -> Core.Expr.Tuple (List.map (strict ~tail:false) args)
    | Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches; occurrence = occ} ->
      let scrut = strict ~tail:false scrut in
      let e' =
        Core.Expr.Match {scrutinee_type = ty; scrutinee = scrut; branches = Array.map
              (fun ({Core.Match.Branch.binders = ids; result_type = rty; body = body; _} as br) ->
                {br with Core.Match.Branch.body = inner ~expected:rty (List.length ids) body} )
              branches; occurrence = occ}
      in
      (* A match whose value is not the result, with a branch that recurses,
         is itself bound: the call ends its branch, so no binding inside the
         branch can take it out of the expression around the match. *)
      if (not tail) && branch_reaches_call cx group ~depth branches then
        let {Core.Match.Branch.result_type = rty; _} = branches.(0) in
        take e' rty
      else e'
    | Core.Expr.Let {binder = id; binder_type = ty; value = rhs; body; occurrence = occ} ->
      (* A right-hand side that is the call, a local fixpoint applied there
         that recurses into the group, or a match ending in one, is already
         bound. *)
      let rhs =
        match rhs with
        | Core.Expr.Apply {callee = f; arguments = args} when group_call rhs <> None || enters_group f ->
          Core.Expr.Apply {callee = strict ~tail:false f; arguments = List.map (strict ~tail:false) args}
        | Core.Expr.Match _ -> strict ~tail:true rhs
        | _ -> strict ~tail:false rhs
      in
      let group =
        match rhs with
        | Core.Expr.Fixpoint {members = [|{body = fn; _}|];
                              occurrence = o; _} when Core_passes.Splices.is_entered_copy group.splices o ->
          (* A partner's copy the machine enters stands for the partner: its
             calls are the group's. *)
          {group with locals = (depth + 1, [|{type_ = ty; arity = Base.Core_util.nb_lams fn}|]) :: group.locals}
        | _ -> group
      in
      Core.Expr.Let {binder = id;
                     binder_type = ty;
                     value = rhs;
                     body = inner ~group ?expected:(if tail then expected else None) 1 body;
                     occurrence = occ}
    | Core.Expr.Lambda {parameter = id; parameter_type = ty; body} ->
      Core.Expr.Lambda {parameter = id; parameter_type = ty; body = inner 1 body}
    | Core.Expr.Fixpoint rec_group ->
      let i = rec_group.selected
      and ids = Core.Recursion.Group.functions rec_group
      and bodies = Core.Recursion.Group.bodies rec_group
      and occ = rec_group.occurrence in
      let n = Array.length ids in
      let fns = Array.mapi (fun j (_, ty) -> {type_ = ty; arity = Base.Core_util.nb_lams bodies.(j)}) ids in
      let group = {group with locals = (depth + n, fns) :: group.locals} in
      Core.Expr.Fixpoint (Core.Recursion.Group.of_arrays ~selected:i ids (Array.map (inner ~group n) bodies) occ)
    | Core.Expr.Cofixpoint rec_group ->
      let i = rec_group.selected
      and ids = Core.Recursion.Group.functions rec_group
      and bodies = Core.Recursion.Group.bodies rec_group
      and occ = rec_group.occurrence in
      Core.Expr.Cofixpoint
        (Core.Recursion.Group.of_arrays ~selected:i ids (Array.map (inner ~group (Array.length ids)) bodies) occ)
    | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
      Core.Expr.Coerce {source_type = from;
                        target_type = into;
                        value = strict ~reading:(Coerced into) ~tail a;
                        occurrence = mocc}
    | Core.Expr.Boxed_value {value = a; occurrence = mocc} ->
      Core.Expr.Boxed_value {value = strict ~tail a; occurrence = mocc}
    | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
      Core.Expr.Lambda_group_barrier {value = strict ~tail a; occurrence = mocc}
    | _ -> e
  in
  let body = strict ~tail:true e in
  let calls = List.rev !taken in
  let k = List.length calls in
  (* The [i]th let sees the [i - 1] before it; the body sees all [k]. *)
  let rec wrap i = function
    | [] -> replace_placeholders (fun j -> Core.Expr.fresh_rel (k - j + 1)) (Base.Core_util.ast_lift k body)
    | (call, ty) :: rest ->
      let rhs = replace_placeholders (fun j -> Core.Expr.fresh_rel (i - j)) (Base.Core_util.ast_lift (i - 1) call) in
      Core.Expr.Let {binder = group.fresh ();
                     binder_type = ty;
                     value = rhs;
                     body = wrap (i + 1) rest;
                     occurrence = Core.Occurrence.fresh ()}
  in
  (* The scope from the let at depth [depth] on, what follows a match it
     binds copied into the match's branches, each branch then a scope. *)
  let rec distribute ~depth e =
    let pushed =
      match e, expected with
      | Core.Expr.Let {binder = id;
                       binder_type = ty;
                       value = Core.Expr.Match {scrutinee_type = cty;
                                                scrutinee = scrut;
                                                branches;
                                                occurrence = case_occ};
                       body = rest;
                       occurrence = occ}, Some rty
        when (not (Recursion.match_bound_in_place cty branches)) && branch_reaches_call cx group ~depth branches ->
        into_branches ~fresh:group.fresh ~rty (id, ty, occ) branches rest
        |> Option.map (fun branches ->
               Core.Expr.Match {scrutinee_type = cty; scrutinee = scrut; branches = Array.map
                     (fun ({Core.Match.Branch.binders = ids; result_type = rty; body = b; _} as br) ->
                       { br with
                         Core.Match.Branch.body = scope cx ~group ~depth:(depth + List.length ids) ~expected:rty b } )
                     branches; occurrence = case_occ} )
      | _ -> None
    in
    match pushed, e with
    | Some e', _ -> e'
    | None, Core.Expr.Let {binder = id; binder_type = ty; value = rhs; body; occurrence = occ} ->
      Core.Expr.Let {binder = id;
                     binder_type = ty;
                     value = rhs;
                     body = distribute ~depth:(depth + 1) body;
                     occurrence = occ}
    | None, _ -> e
  in
  distribute ~depth (if k = 0 then body else wrap 1 calls)

(* Whether [r] is loopified: by its own name, or, made a method, where its
   inductive's methods are (see {!Base.Table.loopifies_methods_of}) and its own
   name does not decline. *)
let loopified ~methods r =
  match Method_registry.is_registered_method methods r with
  | Some (ind, _) -> Base.Table.loopifies_methods_of ind && Base.Table.loopifies_method r
  | None -> Base.Table.should_loopify r

(* The body [b] of a declaration of type [ty], normalized against the
   top-level functions [globals] it recurses through, in a program of effect
   operations [effects] whose partners splicing decided [splices]. *)
let body cx ~effects ~splices ~globals ty b =
  scope cx ~group:{globals;
                own_tvars = Base.Core_util.type_maxvar ty;
                locals = [];
                fresh = temporaries ();
                effects;
                splices} ~depth:0 b

let decl cx ~effects ~splices ~methods = function
  | Core.Decl.Recursive_group fds when Core.Nonempty.exists (fun (fd : Core.Recursion.Definition.t) ->
    loopified ~methods fd.entity) fds ->
    (* A group is normalized whole: loopification inlines one member's
       partners into it, whether or not they are loopified themselves. *)
    let globals = List.map (fun (fd : Core.Recursion.Definition.t) -> fd.entity) (Core.Nonempty.to_list fds) in
    Core.Decl.Recursive_group
      (Core.Nonempty.map
         (fun (fd : Core.Recursion.Definition.t) ->
           {fd with Core.Recursion.Definition.body = body cx ~effects ~splices ~globals fd.type_ fd.body} )
         fds)
  | Core.Decl.Value {entity = r; body = b; type_ = ty} when loopified ~methods r ->
    (* No recursion of its own, but a local fixpoint in it is loopified. *)
    Core.Decl.Value {entity = r; body = body cx ~effects ~splices ~globals:[] ty b; type_ = ty}
  | d -> d

(* A definition of type [ty] as it is generated: binding a parameter at each
   of its type's arrows ({!Base.Type_util.eta_parameters}), the body it writes
   applied to the ones it does not, at each that extraction did not erase. *)
let eta_body ty b =
  match b with
  | Core.Expr.Axiom_value _ | Core.Expr.Runtime_error _ -> b
  | _ ->
    let ty = Base.Core_util.type_simpl ty in
    let params, body = Base.Type_util.collect_typed_lams ty b in
    match Base.Type_util.eta_parameters ty params with
    | [] -> b
    | missing ->
      let args =
        List.rev
          (List.filter_map
             (fun (i, (_, t)) -> if Base.Type_util.erased_by_extraction t then None else Some (Core.Expr.fresh_rel (i + 1)))
             (List.mapi (fun i x -> (i, x)) missing) )
      in
      Base.Core_util.named_lams (missing @ params)
        (Base.Core_util.apply_eta_args (Base.Core_util.ast_lift (List.length missing) body) args)

(* Every local fixpoint in [e] as {!eta_body} generates a definition: a
   function of the group binding a parameter at each arrow of its type.  A
   local [fix go (l : list nat) (acc : nat -> nat) : nat -> nat] is lowered
   as a function, and lowering counts its parameters by its lambdas, its
   calls by its type: [go l acc 1] would pass three arguments to a function
   of two, returning [nat]. *)
let rec eta_local_fixpoints e =
  match Base.Core_util.ast_map eta_local_fixpoints e with
  | Core.Expr.Fixpoint group ->
    let types = Core.Recursion.Group.functions group in
    Core.Expr.Fixpoint
      (Core.Recursion.Group.with_bodies group
         (Array.mapi (fun i b -> if writes_leading_domains (snd types.(i)) b then eta_body (snd types.(i)) b else b)
            (Core.Recursion.Group.bodies group)))
  | e -> e

(* Whether the lambdas of [b] stand for the leading domains of [ty], each
   erased where its domain is, and the domains past them are values of a
   type extraction kept: the parameters {!eta_body} adds are then the
   trailing ones, each a value the function is applied to.  A group typed
   from its declared types ({!Rocq_to_core.Extraction}'s [erased_fix_types])
   may write fewer; a well-founded fixpoint's [Fix_F] has an accessibility
   proof past its argument, typed [Unknown], which no call passes. *)
and writes_leading_domains ty b =
  let ty = Base.Core_util.type_simpl ty in
  let params, _ = Base.Type_util.collect_typed_lams ty b in
  let doms = Base.Type_util.core_domains ty in
  let n = List.length params in
  let erased = Base.Type_util.erased_by_extraction in
  List.compare_lengths params doms < 0
  && List.for_all2 (fun (_, p) d -> erased p = erased d) (List.rev params) (List.filteri (fun i _ -> i < n) doms)
  && List.for_all (fun d -> not (erased d || Base.Core_util.has_unknown d)) (List.filteri (fun i _ -> i >= n) doms)

(* A definition that computes before taking every parameter its type gives
   it: [mk fs := fold_right compose id fs] at [list (nat -> nat) -> nat ->
   nat] folds once and returns the closure.  Generated, it takes all of
   them ({!eta_body}), so [mk fs] passed or bound as a value would fold
   again at every application, where Rocq folds once.  The partial
   application is instead the body at the arguments written: the fold is
   then a call whose result is the closure, made where it stands.

   A candidate is a top-level definition outside any functor, not
   recursive, whose body, past the parameters it writes, is a call filling
   its callee (or a let or match reaching one), and small enough to copy. *)
type prefix_work = {params : int; ty : Core.Type.t; body : Core.Expr.t}

let max_inlined_prefix = 60

let prefix_work_candidates struc =
  let defs = ref [] in
  let rec elems l =
    List.iter
      (fun (_, se) ->
        match se with
        | Core.Module.Structure_item.Declaration (Core.Decl.Value {entity = r; body = b; type_ = ty})
          when not (Base.Table.is_custom r) ->
          let params, inner = Base.Type_util.collect_typed_lams (Base.Core_util.type_simpl ty) b in
          let n = List.length params in
          if n > 0 && Base.Type_util.eta_parameters (Base.Core_util.type_simpl ty) params <> []
             && Base.Core_util.ast_size inner <= max_inlined_prefix
          then defs := (r, ({params = n; ty; body = b}, inner)) :: !defs
        | Core.Module.Structure_item.Module {Core.Module.expr = Core.Module.Expr.Structure {items = l; _}; _} ->
          elems l
        | _ -> () )
      l
  in
  List.iter (fun (_, l) -> elems l) struc;
  let value_arity g =
    match Base.Table.find_type g with
    | ty -> List.length (Base.Type_util.core_value_domains (Base.Core_util.type_simpl ty))
    | exception Not_found -> max_int
  in
  let written_args args = List.length (List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args) in
  (* [known] are the candidates found so far: a call that stops where one
     of them stops computing does its work too. *)
  let rec does_work known = function
    | Core.Expr.Apply {callee = Core.Expr.Global {callee = g; _}; arguments = args} ->
      (not (Base.Table.is_custom g))
      && ( written_args args >= value_arity g
         || match Core.Ref.User.Map.find_opt g known with
            | Some {params; _} -> List.length args = params
            | None -> false )
    | Core.Expr.Let {value; body; _} -> does_work known value || does_work known body
    | Core.Expr.Match {branches; _} ->
      Array.exists (fun {Core.Match.Branch.body = b; _} -> does_work known b) branches
    | Core.Expr.Coerce {value = a; _} | Core.Expr.Boxed_value {value = a; _}
    | Core.Expr.Lambda_group_barrier {value = a; _} ->
      does_work known a
    | _ -> false
  in
  let rec settle known =
    let known' =
      List.fold_left
        (fun m (r, (d, inner)) -> if does_work known inner then Core.Ref.User.Map.add r d m else m)
        known !defs
    in
    if Core.Ref.User.Map.cardinal known' = Core.Ref.User.Map.cardinal known then known else settle known'
  in
  settle Core.Ref.User.Map.empty

(* [b] applied to exactly its [n] leading lambdas' arguments [args]: a
   variable or a literal substituted, any other bound by a let, so it is
   still evaluated once, where the application stood, even when the body
   reads it under a lambda. *)
let beta b args =
  let params, body = Base.Core_util.collect_lams b in
  let n = List.length args in
  let outer = List.rev params in
  let now = List.filteri (fun i _ -> i < n) outer in
  let rest = List.rev (List.filteri (fun i _ -> i >= n) outer) in
  let body = Base.Core_util.named_lams rest body in
  let rec trivial = function
    | Core.Expr.Bound_variable _ | Core.Expr.Global _ | Core.Expr.Erased_value _ | Core.Expr.Numeral _
    | Core.Expr.UInt63 _ | Core.Expr.Float64 _ | Core.Expr.String _ ->
      true
    | Core.Expr.Coerce {value = a; _} | Core.Expr.Boxed_value {value = a; _} -> trivial a
    | _ -> false
  in
  (* Innermost first, each step substituting [Bound_variable 1]; the
     argument for the [i]th parameter (outermost first) lives outside the
     [n - i - 1] parameters still bound around it. *)
  let rec go body i = function
    | [] -> body
    | (a, (id, ty)) :: more ->
      let a = Base.Core_util.ast_lift (n - i - 1) a in
      let body =
        if trivial a then Base.Core_util.ast_subst a body
        else Core.Expr.Let {binder = id; binder_type = ty; value = a; body; occurrence = Core.Occurrence.fresh ()}
      in
      go body (i + 1) more
  in
  go body 0 (List.rev (List.combine args now))

(* The use's copy of a candidate's body, at the type arguments it wrote:
   [None] where it did not write one for every variable the type mentions. *)
let body_at (use : Core.Global_use.t) {ty; body; _} =
  let n = Base.Core_util.type_maxvar ty in
  if n = 0 then Some body
  else if Base.Core_util.written_covers use n then
    Some (Base.Core_util.instantiate_body ~reader:"normalize.prefix_work" use body)
  else None

(* [body] under one more binder, outside the one it reads as
   [Bound_variable 1]. *)
let lift_under_one body =
  match Base.Core_util.ast_lift 1 (Core.Expr.Lambda {parameter = Core.Binder_name.Anonymous;
                                                     parameter_type = Core.Type.Unknown; body}) with
  | Core.Expr.Lambda {body; _} -> body
  | _ -> assert false

(* [let x := value in body] with the lets [value] starts with taken out
   first: a let whose value is a let is a shape lowering does not keep its
   scopes straight in. *)
let rec float_let binder binder_type occurrence value body =
  match value with
  | Core.Expr.Let {binder = y; binder_type = yt; value = v; body = b; occurrence = yo} ->
    Core.Expr.Let {binder = y; binder_type = yt; value = v; occurrence = yo;
                   body = float_let binder binder_type occurrence b (lift_under_one body)}
  | _ -> Core.Expr.Let {binder; binder_type; value; body; occurrence}

let rec inline_prefix_work cands e =
  match e with
  | Core.Expr.Let {binder; binder_type; value; body; occurrence} ->
    let value = inline_value cands value in
    float_let binder binder_type occurrence value (inline_prefix_work cands body)
  | _ -> (
    match inline_value cands e with
    | Core.Expr.Let _ -> declined cands e
    | e' -> e' )

(* [e], a partial application of a candidate copied in where it stands, the
   copy starting with a let where its arguments need one. *)
and inline_value cands e =
  match e with
  | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} -> (
    let args = List.map (inline_prefix_work cands) args in
    match Core.Ref.User.Map.find_opt use.callee cands with
    | Some ({params; _} as d) when List.length args = params -> (
      match body_at use d with
      | Some b -> inline_value cands (Core_passes.Fresh_occurrences.term (beta b args))
      | None -> Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} )
    | _ -> Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} )
  | Core.Expr.Let {binder; binder_type; value; body; occurrence} ->
    let value = inline_value cands value in
    float_let binder binder_type occurrence value (inline_prefix_work cands body)
  | _ -> Base.Core_util.ast_map (inline_prefix_work cands) e

(* [e] where its own copy would start with a let: only its subterms are
   rewritten. *)
and declined cands e =
  match e with
  | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = args} ->
    Core.Expr.Apply {callee = Core.Expr.Global use; arguments = List.map (inline_prefix_work cands) args}
  | _ -> Base.Core_util.ast_map (inline_prefix_work cands) e

let eta_expand struc =
  let cands = prefix_work_candidates struc in
  let struc =
    if Core.Ref.User.Map.is_empty cands then struc
    else
      Core_passes.Modutil.map_struct_decls
        (function
          | Core.Decl.Value {entity = r; body = b; type_ = ty} ->
            Core.Decl.Value {entity = r; body = inline_prefix_work cands b; type_ = ty}
          | Core.Decl.Recursive_group fds ->
            Core.Decl.Recursive_group
              (Core.Nonempty.map
                 (fun (fd : Core.Recursion.Definition.t) ->
                   {fd with Core.Recursion.Definition.body = inline_prefix_work cands fd.body} )
                 fds )
          | d -> d )
        struc
  in
  let eta_body ty b = eta_body ty (eta_local_fixpoints b) in
  Core_passes.Modutil.map_struct_decls (function
    | Core.Decl.Value {entity = r; body = b; type_ = ty} ->
      Core.Decl.Value {entity = r; body = eta_body ty b; type_ = ty}
    | Core.Decl.Recursive_group fds ->
      Core.Decl.Recursive_group
        (Core.Nonempty.map
           (fun (fd : Core.Recursion.Definition.t) ->
             {fd with Core.Recursion.Definition.body = eta_body fd.type_ fd.body})
           fds )
    | d -> d )
    struc

let let_lambdas =
  Core_passes.Modutil.map_struct_decls (function
    | Core.Decl.Value {entity = r; body = b; type_ = ty} ->
      Core.Decl.Value {entity = r; body = Elaborate.generated_definition ty b; type_ = ty}
    | Core.Decl.Recursive_group fds ->
      Core.Decl.Recursive_group
        (Core.Nonempty.map
           (fun (fd : Core.Recursion.Definition.t) ->
             {fd with Core.Recursion.Definition.body = Elaborate.generated_definition fd.type_ fd.body} )
           fds)
    | d -> d )

(* The methods the structure's functions become. *)
let methods_of cx struc = Method_registry.create ~ret_is_erased:cx.return_type_is_erased struc

(* The effect operations are those of the program being normalized, read
   off it first ({!Effects.analyze}): a bind is sequencing only where
   the declaration it is written in erases its monad. *)
let structure cx (program : Core_passes.Phase.normalizing) : Core_passes.Phase.normalizing =
  let methods = methods_of cx program.structure in
  let {Core_passes.Phase.structure = struc; splices} =
    Recursion.splice_partners ~suspension:cx.suspension ~loopified:(loopified ~methods)
      ~inlines:(fun r -> Method_registry.is_registered_method methods r = None)
      program
  in
  {structure = Core_passes.Modutil.map_struct_decls
    (decl cx ~effects:(Effects.analyze struc) ~splices ~methods:(methods_of cx struc)) struc;
   splices}
