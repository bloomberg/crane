(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Type conversion for translation: MiniML types to C++ types, erasure and
    boxing judgements, the C++ types binders are assigned, template arguments,
    and coercions between representations.  Reaches expression generation
    only through {!type_term_arg}. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Translation_support
open Core_query

(** [promoted_var_binding var_id] -- what the scope says the promoted variable
    named [var_id] stands for, by name.  Reached from a globref through
    {!promoted_var_resolution}, and by name alone where only the name survives
    -- see {!Table.ind_promoted_params}. *)
let promoted_var_binding var_id =
  let r = Option.map snd
    (List.find_opt
       (fun (n, _) -> Id.equal n var_id)
       (!tctx).promoted_var_map ) in
  r

(** [ind_promoted_type_args g] -- the leading template arguments a mention of
    the type [g] passes for the promoted variables its definition names.  [g]
    is an inductive, whose payloads name them, or a type-level [Definition],
    whose body does.

    Such a variable is a type the definition does not own: it belongs to
    whichever instance was in scope where it was declared, so it is a
    parameter there (see {!Table.promoted_type_params} and its uses in
    [Cpp_ind] and [Gen_decls.gen_type_alias]) and an argument at every use.  Inside the inductive's own
    declaration the argument is that parameter, which is what the [Tpromoted]
    fallback spells; a scope that knows no instance spells the file-scope
    alias, as it did before there was a parameter at all. *)
let ind_promoted_type_args_ir g : Cpp_ir.Lowered.Type.t list =
  List.map
    (fun v ->
      match promoted_var_binding v with
      | Some t -> t
      | None -> Promoted_member v )
    (Table.promoted_type_params g)

(** Strip the const/reference decoration a parameter type carries, leaving the
    type of the value the binder denotes.  [const auto &] assigns [Tauto]:
    a deduced parameter is never physically a box. *)
let rec strip_param_wrappers : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Reference (_, t) | Const t -> strip_param_wrappers t
  | t -> t

(** Whether the binder at de Bruijn index [i] was typed by a pattern match.
    A binding-site assignment does not overwrite such an entry: the
    instantiation the branch pinned down is the more precise of the two. *)
let pinned_by_pattern i =
  match IntMap.find_opt i (!tctx).cpp_binder_types with
  | Some (_, Bpattern) -> true
  | _ -> false

(** [recover_carrier_result ~fun_ty ~n_args ~want expr] converts a call whose
    declared result is a carrier applied to a type variable -- [M A], a
    {!Miniml.Tapp} -- into the same carrier at the element the position means.

    A dictionary stores its methods monomorphically, so such a result comes
    back at the erased element whatever the call's own arguments were, and only
    an elementwise conversion gets from [M<std::any>] to [M<Nat>].  [fun_ty] is
    the callee's ML function type, or [None] where the caller knows the
    question does not arise. *)
let recover_carrier_result ~fun_ty ~n_args ~(want : Cpp_ir.Lowered.Type.t option) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let carrier_result =
    match Option.map (ml_codomain_after n_args) fun_ty with
    | Some (Some (Miniml.Tapp _)) -> true
    | _ -> false
  in
  match want with
  (* A reified monadic carrier is a [shared_ptr], not a container: it has no
     elements to walk, and getting from one element type to another is the
     reification path's business, not a cast's. *)
  | Some (Shared_pointer _) -> expr
  | Some want when carrier_result && not (Cpp_ir.Types.prints_as_any want) -> Container_cast (want, expr, false)
  | _ -> expr

(** The C++ type the binder at de Bruijn index [i] was decided to have: the
    instantiation a pattern match pinned down where there is one, and
    otherwise the type assigned where the binder was bound. *)
let binder_cpp_type i : Cpp_ir.Lowered.Type.t option =
  Option.map fst (IntMap.find_opt i (!tctx).cpp_binder_types)

(** Wrap [expr] in the [crane_erase_fn] runtime helper, adapting it to the
    erased representation [shape] names (see {!Cpp_ir.Expr.Erase_shape}). *)
let wrap_crane_erase_fn shape (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t = Erase_callable (shape, expr)

(** Re-instantiate a function value that is being adapted for an erased slot:
    the values it will be applied to reached that slot erased too -- a
    [list nat] argument is stored as [List<std::any>], not [List<uint64_t>] --
    so the function has to be taken at the erased instantiation, or the
    adapter would unbox to a shape nothing ever boxed. *)
let erased_fn_instantiation : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Expr.t = function
  | Entity (g, (_ :: _ as tys), xs) -> Entity (g, List.map (fun _ -> Cpp_ir.Type.Any) tys, xs)
  | e -> e

(** [adapter_params ~prefix dom] -- fresh parameters for an adapter lambda,
    one per domain type, in source order.

    An adapter is a lambda whose only job is to call something else with its
    own arguments passed along, so its parameters exist only to be named.
    [prefix] distinguishes the adapters from one another in the generated
    code, and is the caller's to choose. *)
let adapter_params ~prefix dom =
  List.mapi
    (fun i ty -> (ty, Some (Id.of_string (Printf.sprintf "%s%d" prefix i))))
    dom

(** An {!adapter_params} parameter read back as the argument to pass along. *)
let adapter_arg (_, id) : Cpp_ir.Lowered.Expr.t = Local (Option.get id)

(** Whether a position has stated a type concrete enough to recover a box into.
    A slot spelled [std::any] wants the box as it stands, and one still spelled
    as a template parameter has not been stated at all: an [any_cast] there
    would be a guess about an instantiation this site cannot see. *)
let states_unboxed_target_ir into = not (Cpp_ir.Types.prints_as_any into || contains_tvar_ir into)

(** [inline_iife k expr] checks whether [expr] is an IIFE
    ([CPPfun_call(CPPlambda
      { cl_params = \[\];
        cl_body = body;
        _ }, \[\])]).  If so, it replaces
    the final [Sreturn(Some v)] in [body] with [k v] and returns the
    inlined statement list.  Otherwise it falls back to [\[k expr\]].

    Only zero-argument, zero-parameter IIFEs are inlined — parameterised
    lambdas and those with explicit return-type annotations involving
    captures are left untouched, since they may have name-scoping or
    type-deduction side-effects.

    @param k     the statement-level continuation (e.g. [Sreturn], [Sasgn])
    @param expr  the expression produced by [gen_expr] *)
let inline_iife_ir (k : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) (e : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Stmt.t list =
  match e with
  | Call (_, Lambda {params = []; return_type = ret_ty; body; _}, []) when body <> [] ->
    let k_is_return =
      match k (Literal (Int 0)) with Return _ -> true | _ -> false
    in
    if not k_is_return then
      [k (Cpp_ir.Build.iife ret_ty body)]
    else
    let map_all_or_none transform branches =
      let results = List.map transform branches in
      if List.for_all (fun x -> x <> None) results then
        Some (List.filter_map Fun.id results)
      else None
    in
    let rec replace_last_return : Cpp_ir.Lowered.Stmt.t list -> Cpp_ir.Lowered.Stmt.t list option = function
      | [Return (Some v)] -> Some [k v]
      | [Return None] -> None
      | [Throw _] as stmts -> Some stmts
      | [If i] ->
        ( match (replace_last_return i.then_, replace_last_return i.else_) with
        | Some then_br', Some else_br' -> Some [If {condition = i.condition; then_ = then_br'; else_ = else_br'}]
        | _ -> None )
      | [Switch w] ->
        let default' =
          match w.default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun (id, stmts) ->
              Option.map (fun stmts' -> (id, stmts')) (replace_last_return stmts))
            w.branches, default')
        with
        | Some branches', Some default' -> Some [Switch {w with branches = branches'; default = default'}]
        | _ -> None )
      | [Custom_match m] ->
        Option.map
          (fun branches' -> [(Custom_match {m with branches = branches'} : Cpp_ir.Lowered.Stmt.t)])
          (map_all_or_none
            (fun (b : Cpp_ir.Lowered.phase Cpp_ir.Stmt.Custom_match.branch) ->
              Option.map (fun stmts' -> {b with body = stmts'}) (replace_last_return b.body))
            m.branches)
      | [Match (scrut, branches, default)] ->
        let default' =
          match default with
          | Some stmts -> Option.map (fun s -> Some s) (replace_last_return stmts)
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun (br : Cpp_ir.Lowered.phase Cpp_ir.Stmt.Match.branch) ->
              Option.map (fun body' -> { br with body = body' }) (replace_last_return br.body))
            branches, default')
        with
        | Some branches', Some default' ->
          Some [Match (scrut, branches', default')]
        | _ -> None )
      | stmt :: rest when rest <> [] ->
        Option.map (fun rest' -> stmt :: rest') (replace_last_return rest)
      | _ -> None
    in
    ( match replace_last_return body with
    | Some stmts -> stmts
    | None -> [k (Cpp_ir.Build.iife ret_ty body)] )
  | expr -> [k expr]

(** The C++ type a position is being generated into: what it states
    ([expected], a generator's [?expected_ty]), and where it states nothing,
    the enclosing function's return type -- which a tail position lands in.
    The one place that precedence is written down, so that "the type this
    position expects" cannot mean the position at one site and the enclosing
    return type at another. *)
let position_cpp_ty_ir (expected : Cpp_ir.Lowered.Type.t option) =
  match expected with
  | Some _ as t -> t
  | None -> current_cpp_return_type_ir ()

(** A callable handed to a parameter the callee declared at one of its own
    type variables has to arrive under a name: a closure's type cannot be
    spelled, so it can never agree with the same type variable as deduced
    from another argument -- [f (nat -> nat) S []], where the list argument
    settles the variable on [std::function<uint64_t(uint64_t)>].
    {!Minicpp.CPPfn_value} gives the closure that very type, deduced from it.

    The parameter type must be the callee's own, before this call site's
    instantiation is substituted into it: it is the template parameter that
    C++ has to deduce, not what it should deduce to. *)
let name_fn_arg_for_tvar_param param_ml_ty (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match (resolve_tmeta param_ml_ty, expr) with
  | Miniml.Tvar (_, _), Lambda _ -> Function_value expr
  | _ -> expr

(** Whether [expr] is a pair recovered from a box, i.e. one whose [any_cast]
    named the erased shape [pair<any, any>] and whose components are therefore
    boxes in their own right. *)
let reads_recovered_pair : Cpp_ir.Lowered.Expr.t -> bool = function
  | Any_cast (Entity_application (g, args, _), _) | Tolerant_any_cast (Entity_application (g, args, _), _) ->
    is_prod_global g && args <> [] && List.for_all Cpp_ir.Types.prints_as_any args
  | _ -> false

(** [yields_boxed_component expr] -- whether [expr] reads a component out of a
    pair that was itself recovered from a box, and so hands back a
    [std::any] however concrete its ML type looks.

    A boxed pair stores each component separately boxed, so recovering it
    lands on [pair<any, any>] and [.first] on that is still a box.  The
    accessor path in {!gen_expr_custom} builds exactly this shape, and the
    let-binding and tail-position paths ask here rather than being told out of
    band: the emitted expression is the evidence, so no flag has to be
    threaded from producer to consumer. *)
let yields_boxed_component : Cpp_ir.Lowered.Expr.t -> bool = function
  | Call (_, Entity (_, _, Some {inline = Some {shape = Pair_projection _; _}; _}), [arg]) -> reads_recovered_pair arg
  (* The accessor is not always a custom-inline call: a projection out of a
     [std::pair] is a plain member read, and that is the same evidence. *)
  | Access (Dot, arg, _) -> reads_recovered_pair arg
  | _ -> false

(** {!instantiate_at_call} at the type arguments [use] wrote, read by the
    callee's scheme variables. *)
let instantiate_use_at_call use value_args ty =
  Mlutil.instantiate_written ~reader:"instantiate_use_at_call" use
    (with_dict_carrier ~lex:(current_lexenv ()) ~caller:!Table.current_decl_ref use.callee
       value_args ty )

(** What an application of a global yields, as an ML type.

    The callee's declared type says it, once instantiated the way the call
    instantiates it: [tys] for its own [forall]s, and the dictionary argument
    for the class parameter its parameter types spell as the carrier applied.
    That is the same pair of substitutions {!gen_app}'s [subst_ml_ty] makes,
    read at the codomain instead of at a domain.

    [None] where the callee has no recorded type, or fewer value arrows than
    the call has value arguments -- a partial application returns a function,
    which is not what the callers of this want. *)
let ml_app_result_type (f : ml_ast) (args : ml_ast list) : ml_type option =
  let ( let* ) = Option.bind in
  match f with
  | MLglob ({callee = id; _} as use) ->
    let value_args =
      List.filter (function MLdummy _ -> false | _ -> true) args
    in
    let* ty = find_type_opt id in
    Ml_type_util.ml_codomain_after (List.length value_args)
      (instantiate_use_at_call use value_args ty)
  | _ -> None

(** The binder a match scrutinee names, seen through the wrappers that leave
    the value alone: a magic cast, and a dependent instantiation.  A payload
    whose type is written [P x] appears applied to its witness, but a binder
    of non-function type is no callable: the application names the binder
    itself, and that is where the value's C++ type was pinned down. *)
let rec scrutinee_binder = function
  | MLrel (i, _) -> Some i
  | MLmagic (_, e, _) -> scrutinee_binder e
  | MLapp (h, _) when not (scrutinee_head_is_callable h) ->
    scrutinee_binder h
  | _ -> None

(** Whether a term in head position really is a function being applied, as
    opposed to a binder that a dependent type spells applied to its index. *)
and scrutinee_head_is_callable h =
  match scrutinee_binder h with
  | Some i ->
    let rec is_arrow = function
      | Miniml.Tmeta {contents = Some t} -> is_arrow t
      | Miniml.Tarr _ -> true
      | _ -> false
    in
    (match get_env_type_opt i with Some t -> is_arrow t | None -> true)
  | None -> true

(** Test whether a C++ expression is "trivial" — a simple variable or member
    access that can safely be duplicated without side effects.  Non-trivial
    expressions (function calls, constructor applications, etc.) should be
    cached in a temporary when the custom match template uses [%scrut] more
    than once.  A member access or dereference is trivial only as far as the
    object it reads is: [mk(n).sub] calls [mk] at every mention. *)
let rec is_trivial_scrut_ir : Cpp_ir.Lowered.Expr.t -> bool = function
  | Local _ | Scope _ | Type_member _ | Enum_value _ | Entity _ -> true
  | Member (e, _) | Project (e, _, _) | Access (_, e, _) | Dereference e -> is_trivial_scrut_ir e
  | _ -> false

(** The C++ type a pattern match pinned down for the binder at de Bruijn index
    [i], if this branch pinned one.  A binding-site assignment is not an
    answer here: it says what the binder's ML type converts to, which for a
    field read out of an erased carrier is the type the value {e would} have
    had, not the [std::any] it is actually stored as. *)
let pattern_binder_type i : Cpp_ir.Lowered.Type.t option =
  match IntMap.find_opt i (!tctx).cpp_binder_types with
  | Some (t, Bpattern) -> Some t
  | _ -> None

(** [convert_ml_type_to_cpp_type] only resolves [Tvar] indices within
    [tvars]; anything out of range comes back as [Tvar (Tv_index (_, None))], which
    prints as a bogus, undeclared template parameter name (e.g. "T3").
    Normalize those to [Topaque]: the variable was quantified somewhere we
    cannot see, so [std::any] is the only spelling available, but nothing here
    establishes that the value is actually boxed. *)
let rec erase_unresolved_tvars_ir : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Variable (Index (_, None)) -> Obligation Opaque_type
  | Entity_application (g, ts, es) -> Entity_application (g, List.map erase_unresolved_tvars_ir ts, es)
  | Function (dom, cod) ->
    Function (List.map erase_unresolved_tvars_ir dom, erase_unresolved_tvars_ir cod)
  | Shared_pointer t -> Shared_pointer (erase_unresolved_tvars_ir t)
  | Reference (k, t) -> Reference (k, erase_unresolved_tvars_ir t)
  | t -> t

(** Extract block template info from an inline custom expression.
    Returns [Some(ref, template, args, tyargs)] if the expression is
    an inline custom whose template contains [%result]. *)
let extract_block_template_ir : Cpp_ir.Lowered.Expr.t -> _ = function
  | Entity (ref, tys, Some ci) -> begin
    match ci.inline with
    | Some {form = Block; text = tmpl; _} -> Some (ref, tmpl, [], tys)
    | _ -> None
    end
  | Call (_, Entity (ref, tys, Some ci), args) -> begin
    match ci.inline with
    | Some {form = Block; text = tmpl; _} -> Some (ref, tmpl, args, tys)
    | _ -> None
    end
  | _ -> None

(** Whether the statements a let-binding's right-hand side generated assign a
    value that is really a box.  The right-hand side is generated as an
    assignment, so the bound value is the one expression in it. *)
let stmts_yield_boxed : Cpp_ir.Lowered.Stmt.t list -> bool = function
  | [Bind_variable (_, _, v)] -> yields_boxed_component v
  | _ -> false

(** Whether the generated code [stmts] lets the local fixpoint [target_id]
    escape: names it other than as the callee of a direct call
    [CPPfun_call (CPPvar target_id, args)], or names it at all inside a
    {!Closure}.  Core decides this ({!Analyze_closures}); the generated code
    is only the oracle [CRANE_CHECK_IR] checks it against. *)
let fixpoint_escapes_in_stmts_ir target_id (stmts : Cpp_ir.Lowered.Stmt.t list) =
  let rec check_expr (e : Cpp_ir.Lowered.Expr.t) =
    match e with
    | Call (_, Local id, args) when Id.equal id target_id ->
      List.exists check_expr (List.rev args)
    | Local id when Id.equal id target_id -> true
    | Lambda {body; capture = Runs_in_place; _} -> check_stmts body
    | Lambda {body; capture = Stored; _} ->
      let rec has_var_in_expr (e : Cpp_ir.Lowered.Expr.t) =
        match e with
        | Local id when Id.equal id target_id -> true
        | _ ->
          let found = ref false in
          let fe e' = if not !found then found := has_var_in_expr e'; e' in
          let fs s' = if not !found then found := has_var_in_stmt s'; s' in
          ignore (Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:fe ~stmt:fs ~type_:Fun.id ()) e);
          !found
      and has_var_in_stmt s =
        let found = ref false in
        let on_expr e = if not !found then found := has_var_in_expr e in
        let on_stmts ss =
          if not !found then found := List.exists has_var_in_stmt ss
        in
        Cpp_ir.Subterms.stmt ~expr:on_expr ~stmts:on_stmts s;
        !found
      in
      List.exists has_var_in_stmt body
    | _ ->
      let found = ref false in
      let fe e = if not !found then found := check_expr e; e in
      ignore (Cpp_ir.Map.expr (Cpp_ir.Map.make ~expr:fe ~stmt:Fun.id ~type_:Fun.id ()) e);
      !found
  and check_stmt s =
    let found = ref false in
    let on_expr e = if not !found then found := check_expr e in
    let on_stmts ss = if not !found then found := check_stmts ss in
    Cpp_ir.Subterms.stmt ~expr:on_expr ~stmts:on_stmts s;
    !found
  and check_stmts ss = List.exists check_stmt ss
  in
  check_stmts stmts

(** [names_only_scoped_tvars ty] -- whether every type variable [ty] spells is
    one this scope declares.  A slot type read off a callee's signature is
    written in the callee's type variables, which name nothing here, so such a
    type cannot be used as the type a use site wants. *)
let names_only_scoped_tvars_ir ty =
  let scope = current_scope_type_names () in
  List.for_all (fun id -> List.exists (Id.equal id) scope) (get_tvars_ir ty)

(** [ty], where this scope can write it: every variable it names is in scope,
    and it is not erased. *)
let spell_in_scope_ir ty =
  if names_only_scoped_tvars_ir ty && not (Cpp_ir.Types.prints_as_any ty) then Some ty else None

(** The variable {!Plan_templates.relax_tt_applied_return} takes out of [id]'s
    template head, if any: the higher-kinded head of an applied codomain that
    only a callback's result otherwise names -- [case_]'s [M] in [M X], which
    the declaration spells [std::invoke_result_t<F0 &, ...>] instead.  Read off
    the Rocq type for the reason {!writable_tvar_count} is. *)
let relaxed_tt_return_var id =
  match find_type_opt id with
  | None -> None
  | Some ml_ty -> (
    match resolve_tmeta (ml_codomain ml_ty) with
    | Miniml.Tapp (h, [ _ ])
      when IntSet.mem h (declared_higher_kinded_tvars ml_ty) ->
      let occurs t = IntSet.mem h (collect_tvars_set IntSet.empty t) in
      let doms = List.map resolve_tmeta (ml_domains ml_ty) in
      (* A callback's result, written as an arrow; a definitional class
         spells its variable in the declaration's parameter list and so names
         it ([MonadIter<T1>]). *)
      let under_arrow d =
        match d with Miniml.Tarr _ -> true | _ -> false
      in
      if
        List.for_all (fun d -> under_arrow d || not (occurs d)) doms
        && List.exists (fun d -> under_arrow d && occurs d) doms
      then Some h
      else None
    | _ -> None )

(** The Rocq type-variable positions a call may still write, given that the
    declaration reorders some of them out of reach.

    {!Plan_templates.relax_applied_return} handles a variable named only by the
    return type -- C++ deduces nothing from a return type -- by giving it the
    producing callback's result as its default and moving it {e last}, since a
    default may only name parameters declared before it.  That pass records
    "nothing supplies this signature's arguments explicitly, so the order is
    free", and for a lifted helper that is true.  For a class method it is not:
    [tfmap] is called with its Rocq arguments written out.

    Once such a variable has moved, every position from it onwards is
    unreachable positionally -- reaching it would mean spelling the synthesised
    callable parameter that now precedes it, which is deduced and has no Rocq
    argument to spell.  So the writable prefix ends there.

    The condition is read off the Rocq type rather than the emitted
    declaration, which a call site cannot consult ({!Table.census}'s rule that
    planning decides and emission reads): the variable occurs in the
    codomain, and every domain occurrence of it is under an arrow -- that is,
    it is a callback's result, which is exactly the parameter the declaration
    collapses to a deduced callable and stops naming. *)
let writable_tvar_count id =
  let ( let* ) o f = match o with None -> None | Some x -> f x in
  let* ml_ty = find_type_opt id in
  let n = Mlutil.type_maxvar (type_simpl ml_ty) in
  let occurs v t = IntSet.mem v (collect_tvars_set IntSet.empty t) in
  let cod = resolve_tmeta (ml_codomain ml_ty) in
  (* Only a codomain that {e applies} a variable is relaxed.  [list B] names
     [B] as a plain leading parameter that the call still has to write, and
     dropping it would leave nothing to deduce it from; [T V] is the
     higher-kinded shape {!Plan_templates.relax_applied_return} rewrites. *)
  (* And only a higher-kinded head: a family's application is written plain,
     which the declaration does not relax ({!Plan_templates.relax_applied_return}). *)
  let applied_cod =
    match cod with
    | Miniml.Tapp (h, _) ->
      IntSet.mem h (Ml_type_util.higher_kinded_ml_tvars [ml_ty])
    | _ -> false
  in
  let derived v =
    applied_cod && occurs v cod
    && List.for_all
         (fun d ->
           match resolve_tmeta d with
           | Miniml.Tarr _ -> true
           | d -> not (occurs v d) )
         (ml_domains ml_ty)
    && List.exists (fun d -> occurs v d) (ml_domains ml_ty)
  in
  (* Only a derived {e suffix} may be dropped.  A derived position followed by
     one that is still written cannot be removed without taking that one with
     it, and the later position may be doing work the truncation would undo --
     [iter]'s [R] is derived but its [I] is not, and dropping both loses an
     argument deduction was relying on the first two to place.  Where the list
     cannot be fixed by cutting its tail, it is left exactly as it was. *)
  let rec suffix_start v = if v < 1 then 1 else if derived v then suffix_start (v - 1) else v + 1 in
  Some (suffix_start n - 1)

(** [mk_arity_call ~params ~saturated args] applies a callee to [args], given
    in {e source} order, where the callee's declaration fixes its parameters
    to [params].  [saturated] builds the call, from exactly as many arguments
    as [params] has.

    A call site need not match that arity, and a flat call is wrong whichever
    way it misses.  Arguments past the arity apply to the call's {e result} --
    a binder instantiated at a function type, say -- rather than to the
    callee.  Arguments short of it leave a closure over the ones still to
    come, so the call is eta-expanded instead of emitted shorter than it is
    declared.

    Omit [params] where the declaration is not known: an empty list means a
    nullary callee, which is a different thing and applies every argument to
    the result. *)
let mk_arity_call ?(params : Cpp_ir.Lowered.Type.t list option)
    ~(saturated : Cpp_ir.Lowered.Expr.t list -> Cpp_ir.Lowered.Expr.t) args : Cpp_ir.Lowered.Expr.t =
  match params with
  | None -> saturated args
  | Some params ->
    let arity = List.length params in
    let given = List.length args in
    if given > arity then
      match List.filteri (fun i _ -> i >= arity) args with
      | [] -> saturated args
      | rest -> Cpp_ir.Build.call (saturated (List.filteri (fun i _ -> i < arity) args)) rest
    else if given < arity then
      let waiting = adapter_params ~prefix:"_sat" (List.filteri (fun i _ -> i >= given) params) in
      Cpp_ir.Build.lambda waiting None
        [Return (Some (saturated (args @ List.map adapter_arg waiting)))]
        ~capture:Stored
    else saturated args

(** Whether the generated bodies [funs_with_params] of a local fixpoint
    group let a member of [renamed_ids] escape ({!fixpoint_escapes_in_stmts}):
    the oracle of {!Analyze_closures} for a group's own bodies. *)
let fix_escapes_in_own_bodies_ir renamed_ids funs_with_params =
  List.exists
    (fun (id, _) ->
      List.exists (fun (_, body) -> fixpoint_escapes_in_stmts_ir id body) funs_with_params )
    renamed_ids

(** The inclusive range of a fixed-width C++ integer type, or [None] when the
    spelling is not one this compiler can bound (a user-defined bignum, say).
    Only the spellings a numeral mapping can name are listed; anything else is
    left unchecked rather than guessed at. *)
let cpp_integer_range = function
  | "bool" -> Some (Z.zero, Z.one)
  | "uint8_t" | "unsigned char" -> Some (Z.zero, Z.of_string "255")
  | "uint16_t" | "unsigned short" -> Some (Z.zero, Z.of_string "65535")
  | "uint32_t" | "unsigned" | "unsigned int" ->
    Some (Z.zero, Z.of_string "4294967295")
  | "uint64_t" | "size_t" | "unsigned long" | "unsigned long long" ->
    Some (Z.zero, Z.of_string "18446744073709551615")
  | "int8_t" | "signed char" -> Some (Z.of_string "-128", Z.of_string "127")
  | "int16_t" | "short" -> Some (Z.of_string "-32768", Z.of_string "32767")
  | "int32_t" | "int" ->
    Some (Z.of_string "-2147483648", Z.of_string "2147483647")
  | "int64_t" | "long" | "long long" | "ptrdiff_t" ->
    Some (Z.of_string "-9223372036854775808",
          Z.of_string "9223372036854775807")
  | _ -> None

(** Render a folded literal through a numeral mapping's format string.

    A numeral inductive is unbounded in Rocq but its C++ image usually is not,
    and the format string ([UINT64_C(%n)]) carries the value without checking
    it.  Emitting an out-of-range literal moves the failure to the C++
    compiler at best and wraps silently at worst, so refuse it here, where the
    Rocq definition responsible can still be named. *)
let render_numeral info (n : Z.t) : Cpp_ir.Lowered.Expr.t =
  let cpp_ty = Table.find_custom_opt info.Table.num_ind in
  ( match Option.bind cpp_ty cpp_integer_range with
  | Some (lo, hi) when Z.lt n lo || Z.gt n hi ->
    CErrors.user_err
      (Pp.(
         str "Crane: the literal " ++ str (Z.to_string n)
         ++ str " does not fit in " ++ str (Option.get cpp_ty)
         ++ str ", the C++ type "
         ++ Printer.pr_global info.Table.num_ind
         ++ str " extracts to."))
  | _ -> () );
  Numeral (info.Table.num_ind, {value = n; text = Common.render_template [("%n", Z.to_string n)] info.Table.num_fmt})

(** Whether [r] is a type family over a value -- [sem : idx -> Type] --
    whose applications ML writes without their argument, so that a generic
    declaration erases them where an instantiation can name them. *)
let value_indexed_family r =
  match r with
  (* A class's or record's type field is a function of the instance, not a
     family over a value. *)
  | GlobRef.ConstRef kn
    when Table.is_projection r || Structures.Structure.is_projection kn ->
    false
  | GlobRef.ConstRef _ -> (
    try
      let env = Global.env () in
      let ty, _ = Typeops.type_of_global_in_context env r in
      let prods, head = Reduction.whd_decompose_prod env ty in
      (* A class argument -- a section's [{Pa : Params}] -- is an instance,
         resolved where the family is used, not a value it is indexed by. *)
      let is_class_type t =
        match Constr.kind (fst (Constr.decompose_app t)) with
        | Constr.Ind (ind, _) -> Typeclasses.is_class (GlobRef.IndRef ind)
        | Constr.Const (c, _) -> Typeclasses.is_class (GlobRef.ConstRef c)
        | _ -> false
      in
      Constr.isSort head
      && List.exists
           (fun d ->
             let dty = Context.Rel.Declaration.get_type d in
             let _, h = Reduction.whd_decompose_prod env dty in
             (not (Constr.isSort h)) && not (is_class_type dty) )
           prods
    with _ -> false )
  | _ -> false

(** [t] with the instance's family written where a slot erased it: wherever
    the carrier [carrier] heads a type, an erased argument at a position the
    carrier fills with one of its variables takes that variable's binding in
    [m].  See {!instance_family_binding}. *)
let refine_by_instance_family ((carrier : Cpp_ir.Lowered.Type.t), _, m) (t : Cpp_ir.Lowered.Type.t) :
    Cpp_ir.Lowered.Type.t =
  match carrier with
  | Entity_application (h, cargs, _) ->
    Cpp_ir.Types.map
      (fun (t : Cpp_ir.Lowered.Type.t) ->
        match t with
        | Entity_application (h', args, es) when GlobRef.CanOrd.equal h h' ->
          let n = List.length cargs in
          Entity_application
            ( h',
              List.mapi
                (fun i a ->
                  match List.nth_opt cargs i with
                  | Some (Cpp_ir.Type.Variable (Index (_, Some v) | Named v))
                    when i < n && Cpp_ir.Types.prints_as_any a -> (
                    match List.find_opt (fun (v', _) -> Id.equal v v') m with
                    | Some (_, b) -> b
                    | None -> a )
                  | _ -> a )
                args,
              es )
        | t -> t )
      t
  | _ -> t

(** [param_states_type_args x orig] -- whether the parameter whose Rocq type
    is [orig] constrains the type variables of the global [x] in a way that
    another argument's deduction can conflict with.

    This is a question about the {e declaration} Crane emits for [x], not
    about this call.  Two kinds of parameter say nothing.  A custom-extracted
    callee's C++ is spelled by its mapping, so it has no template parameters
    at all.  And a function-typed parameter is declared as a deduced template
    parameter of its own ({!Common.fun_tparam_name}), so whatever type
    variables its Rocq type mentions, the signature does not state them. *)
let param_states_type_args x orig =
  let rec is_arrow = function
    | Miniml.Tarr _ -> true
    | Miniml.Tmeta {contents = Some t} -> is_arrow t
    | _ -> false
  in
  (not (Table.is_custom x)) && not (is_arrow orig)

(** [erase_type_args_to_any ty] boxes a compound type's arguments but leaves a
    ground type alone: [deque<Nat>] becomes [deque<any>], while [Nat] stays
    [Nat].  This is the shape a box built out of a pattern binder physically
    has, and so the type an [any_cast] recovering it must name.  Deliberately
    weaker than {!Cpp_erasure}'s [erase_type_to_any], which boxes the leaf
    too. *)
let rec erase_type_args_to_any : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Entity_application (g, (_ :: _ as args), ns) -> Entity_application (g, List.map erase_type_args_to_any args, ns)
  | Entity_application (_, [], _) as t -> t
  | In_namespace (ns_g, inner) -> In_namespace (ns_g, erase_type_args_to_any inner)
  | _ -> Any

(** A singleton class's dictionary at the head of a call: the instance
    parameter it is, the class, and the class's one method, as the
    traversal's environment reads it.  Emission takes Core's reading
    ({!Core_elaborate.singleton_dictionary_call}) and checks it against this
    one. *)
let singleton_dictionary env head =
  match strip_magic head with
  | MLrel (i, _) -> (
    match (Common.get_db_name_opt i env, get_env_type_opt i) with
    | Some id, Some (Tglob (c, _, _)) when Common.is_tc_instance_id id ->
      Option.map (fun m -> (id, c, m)) (Table.singleton_class_method c)
    | _ -> None )
  | _ -> None

(** [split_instance_args ~lex args] -- the class dictionaries a call passes,
    the ones an erasure removed left out; how many were removed, which still
    occupy a parameter of the declaration; and the regular arguments. *)
let split_instance_args ~lex args =
  let tc, regular = List.partition (is_typeclass_instance_arg ~lex) args in
  let erased, kept = List.partition (instance_arg_is_erased ~lex) tc in
  (kept, List.length erased, regular)

(** [inline_custom_arg_arity id] is the number of [%aN] term placeholders an
    inline-custom mapping for [id] names -- one past the largest index it
    uses -- or [None] when [id] has no inline-custom mapping.

    A call has to supply exactly that many arguments: the printer drops any
    beyond the last placeholder, and raises on a placeholder it cannot fill. *)
let inline_custom_arg_arity id =
  if not (Table.is_inline_custom id) then None
  else
    match Table.find_custom_opt id with
    | None -> None
    | Some tmpl ->
      let re = Str.regexp "%a\\([0-9]+\\)" in
      let rec scan pos acc =
        match Str.search_forward re tmpl pos with
        | i ->
          scan (i + 1) (max acc (int_of_string (Str.matched_group 1 tmpl) + 1))
        | exception Not_found -> acc
      in
      Some (scan 0 0)

(** [promoted_var_resolution g] -- what the promoted type variable [g] stands
    for here, if the scope says.  A promoted variable is a class's [Type]
    field, and the type that mentions one records the field alone, never the
    instance it belongs to; the enclosing scope is what supplies that, through
    [promoted_var_map].  A variable the scope does not answer has no spelling
    here, which is a different thing from having an erased one. *)
let promoted_var_resolution g =
  match Table.promoted_type_var_name g with
  | Some var_id -> promoted_var_binding var_id
  | None -> None

(** Whether [ty] names a class field the current scope does not resolve, so
    that it would print through the field's file-scope [std::any] alias: a
    type read off another declaration, whose own instance resolved it. *)
let mentions_unresolved_promoted_ir (ty : Cpp_ir.Lowered.Type.t) =
  Cpp_ir.Types.exists
    (fun (t : Cpp_ir.Lowered.Type.t) ->
      match t with
      | Promoted_member v -> promoted_var_binding v = None
      | Entity_application (g, _, _) -> Table.is_promoted_type_var g && promoted_var_resolution g = None
      | _ -> false )
    ty

(** Apply a callee recovered from a bare [std::any], one argument at a time.

    Nothing about a boxed callable says how many arguments it takes: the
    producer's lambda stops at the first codomain that erases, so a value of an
    opaque function type ([nfun 2], a type-level [Fixpoint]) is a chain of unary
    [std::function<std::any(std::any)>]s.  Handing it every argument at once
    would cast it to a signature it was never stored at. *)
let apply_erased_curried ?(box = false) (callee : Cpp_ir.Lowered.Expr.t) arg_exprs : Cpp_ir.Lowered.Expr.t =
  List.fold_left
    (fun (f : Cpp_ir.Lowered.Expr.t) a ->
      let a = if box then Cpp_erasure.converting_ctor_ir Any [a] else a in
      match f with
      (* A callable boxed right here never lost its type: recovering it would
         be a cast straight back to what it already was. *)
      | Box (_, callable) -> Cpp_ir.Build.call callable [a]
      | _ -> Erased_call (f, a) )
    callee arg_exprs

(** Apply a callee whose static C++ type is the erased [std::any].  [std::any]
    is not callable, so the canonical [std::function<std::any(std::any...)>]
    adapter the producer stored via {!box_for_any_slot} is recovered with
    an [any_cast] and each argument is boxed.  The result is a [std::any]. *)
let apply_erased_callee callee arg_exprs =
  apply_erased_curried ~box:true callee arg_exprs

(** Save the current binder-type state for later restoration. *)
let save_erased_env () : binder_env = (!tctx).cpp_binder_types

(** Restore binder-type state saved by {!save_erased_env}. *)
let restore_erased_env saved = tctx := { !tctx with cpp_binder_types = saved }

(** [promoted_tys_of_arity n] is the concrete types the enclosing scope's
    promoted type variables stand for, when there are exactly [n] of them and
    so they can be read as the arguments of an [n]-ary type.  Erased entries
    are dropped, since a promoted variable that resolves to [std::any] says no
    more than the erased annotation it would replace. *)
let promoted_tys_of_arity_ir n =
  match List.filter_map (fun (_, t) -> if Cpp_ir.Types.prints_as_any t then None else Some t)
          (!tctx).promoted_var_map
  with
  | tys when List.length tys = n -> Some tys
  | _ -> None

(** When a lambda literal is about to be stored via [crane_erase_fn] (see the
    [ml_expr_is_function_value] call site in the custom-constructor arg loop),
    the lambda will only ever be invoked with its whole argument boxed as a
    single raw [std::any] (never with the generically-deduced concrete type),
    because that is exactly what [crane_erase_fn]'s CTAD-non-viable fallback
    forwards. If the lambda's own bound parameter [n] is immediately
    pattern-matched via a custom (e.g. pair) match, that match must therefore
    treat the scrutinee as erased — wrap it in [MLmagic] so
    [gen_custom_cpp_case] emits [any_cast<pair<any,any>>(...)] instead of a
    structured binding directly on the (at runtime erased) parameter. Without
    this, a domain type that is a pair with a mix of erased/concrete fields
    (e.g. [S.sem a * unit]) renders the parameter as a generic [auto&], and the
    destructure compiles fine at the OCaml/template level but fails at C++
    instantiation time when [auto&] deduces to [std::any] (structured
    bindings are not valid on [std::any]). *)
let rec mark_own_param_for_pair_erasure n body =
  match body with
  | MLcase (ty, (MLrel (i, _) as scrut), pv, occ) when i = n && is_custom_match pv ->
    MLcase (ty, MLmagic (Mboxed, scrut, Occurrence.fresh ()), pv, occ)
  | MLmagic (m, a, mocc) -> MLmagic (m, mark_own_param_for_pair_erasure n a, mocc)
  | other -> other

(** [field_stores_erased_fn_value_ir ~field_cpp_ty field_types i e] — true when
    constructor field [i] has an abstract type-variable (schema) type — a
    value-dependent field such as the predicate [P] of [sigT A P] — and the
    argument [e] is either a lambda function value or any value landing in a
    slot that is genuinely erased here ([field_cpp_ty], the field type
    instantiated with this call's own type arguments, is [std::any]).

    Such a function's return value is boxed into the field's [std::any] at
    runtime and recovered by consumers with a fixed [any_cast] shape.  To keep
    that shape consistent across every producer of the same Coq type (e.g. the
    "cons" and "nil" productions of a value-dependent [list (nat*nat)] action),
    the function body must be generated in a [Boxed] slot so its
    list/pair/record producers deep-erase to the canonical erased C++ form.
    Without this, a "cons" production built from concrete values would keep a
    concrete element type (e.g. [deque<Prod<Nat,Nat>>]) while the matching
    "nil" production erases to [deque<Prod<any,any>>], and reading the value
    back out of the [std::any] throws [std::bad_any_cast]. *)
let field_stores_erased_fn_value_ir ~(field_cpp_ty : Cpp_ir.Lowered.Type.t option) field_types i e =
  match List.nth_opt field_types i with
  | Some ft ->
    let field_is_abstract_var =
      match ft with Miniml.Tvar (_, _) -> true | _ -> false
    in
    let slot_is_erased =
      match field_cpp_ty with Some ct -> Cpp_ir.Types.prints_as_any ct | None -> false
    in
    let result_is_erased =
      match field_cpp_ty with
      | Some (Function (_, cod)) -> Cpp_ir.Types.exists Cpp_ir.Types.prints_as_any cod
      | Some ct -> Cpp_ir.Types.prints_as_any ct
      | None -> true
    in
    field_is_abstract_var
    && (slot_is_erased
       || (result_is_erased && match strip_magic e with MLlam _ -> true | _ -> false))
  | None -> false

(** Adapt a callable produced with fewer parameters than its use site expects.
    A body like [fun f acc => f acc] is eta-reduced before it reaches here, so
    the lambda takes one argument where the slot's type takes two; the missing
    arguments are supplied by eta-expansion, applying what the shorter lambda
    returns to the arguments it did not take.

    [ml_arity] is how many arguments the slot's MiniML type takes: a lambda
    that takes fewer than its C++ slot but as many as its ML type is curried
    on purpose, not shortened, and is left alone -- as is one whose body
    [returns_a_lambda], having spelled the remaining arguments out itself. *)
let eta_expand_to_expected ?(expected_ty : Cpp_ir.Lowered.Type.t option) ~ml_arity ~returns_a_lambda ~arity
    (f : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match Option.map strip_cpp_ref_const_ir expected_ty with
  | Some (Function (dom, _)) when arity > 0 && ml_arity > arity && List.length dom > arity && not returns_a_lambda ->
    let params = adapter_params ~prefix:"_ee" dom in
    let taken = List.filteri (fun i _ -> i < arity) params in
    let rest = List.filteri (fun i _ -> i >= arity) params in
    let call = List.fold_left (fun acc group -> Cpp_ir.Build.call acc (List.map adapter_arg group)) f [taken; rest] in
    Cpp_ir.Build.lambda params None [Return (Some call)] ~capture:Stored
  | _ -> f

(** The shape a value physically has once it has been through a [std::any]:
    unchanged for a leaf, and one level of template with every argument boxed
    for a compound ([pair<Nat, tup>] becomes [pair<any, any>]).  A compound's
    components are separately boxed, so the erasure stops at one level --
    nesting it would name [pair<any, pair<any, any>>] for a box whose second
    component is itself only a box.  This is the type an [any_cast] reading
    such a value back has to name, whatever concrete type the context has in
    mind for it. *)
let boxed_shape_of_ir : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Entity_application (g, (_ :: _ as args), ns) -> Entity_application (g, List.map (fun _ -> Cpp_ir.Type.Any) args, ns)
  | t -> t

(** How a term argument of a custom type is generated: by {!gen_expr}, which
    fills this in once it is defined.  The one place type conversion calls
    back into expression generation -- a mapped type applied to a term, as a
    fixed-size array is to its length -- so it is the edge the two are
    separated at. *)
let type_term_arg : (env -> ml_ast -> Cpp_ir.Lowered.Expr.t) ref =
  ref (fun _ _ -> CErrors.anomaly (Pp.str "Translation.type_term_arg: unset"))

(** [cpp_ir_of_ml_type env ~ns tvars t] is the C++ type of the ML type [t],
    a variable named as [tvars] names it; [ns] are the inductives whose
    recursive occurrences, at a constructor's storage, are held behind a
    pointer. *)
let rec cpp_ir_of_ml_type
    env
    ?(ns : Ref.User.Set.t = Ref.User.Set.empty)
    (tvars : Id.t list)
    (ml_t : ml_type) : Cpp_ir.Lowered.Type.t =
  (* [ns] is the only source of recursive-storage wrapping.  Most callers
     omit it (defaulting to empty), so types like [List<tree>] stay value
     shaped in function signatures.  Struct-field storage conversion passes the
     owning inductive in [ns], so non-coinductive recursive occurrences at
     constructor storage sites become [shared_ptr]. *)
  match ml_t with
  | Tarr (t1, t2) ->
    (* std::function<F(A)> is already a value type and provides the heap
       indirection needed to break recursive layout cycles.  Always pass an
       empty [ns] for domain and codomain so that recursive self-references
       inside function types stay as value types instead of being wrapped in
       shared_ptr.  The outer field-position wrapping (shared_ptr for direct
       self-ref fields) is handled at the call site, not here. *)
    let t1c = cpp_ir_of_ml_type env tvars t1 in
    (* Reify monadic domain types: itree E R in parameter position becomes
       shared_ptr<ITree<R>> so the tree can be passed as a value. *)
    let t1c = reify_monadic_param_type_ir t1 t1c in
    let t2c = cpp_ir_of_ml_type env tvars t2 in
    (* Skip erased params: isTdummy catches direct Tdummy, is_cpp_dummy_type
       catches Tdummy wrapped in Tmeta (e.g., Tmeta{contents=Some(Tdummy Kprop)}
       which converts to dummy_prop glob). Do NOT use prints_as_any here as it
       also catches Tany (std::any), which is a valid type for universally
       quantified parameters — stripping it would incorrectly collapse (A -> IO)
       into just IO. *)
    if erased_by_extraction t1 || match t1c with Erased _ -> true | _ -> false then
      t2c
    else (
      (* Void-ify unit codomain: function types returning [unit] (directly
         or via monadic wrapper like [itree E unit]) should map to [void]
         to match void-ified function definitions. Check the ML type [t2]
         since the C++ type may still be a monad Tglob, not bare unit. *)
      let voidify_cod (c : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
        if is_cpp_unit_type_ir c then Void
        else if ml_type_is_void_call t2 then Void
        else c
      in
      (* A result the arguments only pin down as a type index is not something
         a template parameter can stand for; erase it. *)
      let voidify_cod c : Cpp_ir.Lowered.Type.t =
        if result_is_index_only_tvar ml_t then Any else voidify_cod c
      in
      match
        t2c
      with
      | Function (l, t) -> Function (t1c :: l, voidify_cod t)
      | _ -> Function (t1c :: [], voidify_cod t2c) )
  | Tglob (g, _, _) when is_void g -> Void
  (* PROMOTED TYPE VARIABLES: Handle references to record fields that were
     "promoted" from value-level fields to type-level parameters.

     A "promoted" field is a Type-valued record field (e.g., [m_carrier : Type]
     in [Record Monoid]) that became a C++ concept type requirement instead of
     a struct field. At usage sites, references to these fields must be treated
     as TYPES, not values.

     Example:
       Coq: [mfold (M : Monoid) (l : list (m_carrier M))]
            Here [m_carrier M] is a TYPE (the carrier type of the monoid M)

       C++: [template <Monoid _tcI0> ... List<typename _tcI0::m_carrier> ...]
            Must qualify as a type, not access as a field: NOT _tcI0->m_carrier

     Three contexts for promoted type vars:
     1. Inside template functions with typeclass params: [promoted_var_map] is
        populated, resolve to qualified types like [typename _tcI0::m_carrier]
     2. Module-level (constructor expressions): Use module aliases ([std::any])
     3. No context: Mark with [Tpromoted] for later resolution *)
  | Tglob (g, ts, _) when Table.is_promoted_type_var g ->
    ( match Table.promoted_type_var_name g with
    | Some var_id ->
      ( match promoted_var_resolution g with
      | Some resolved -> resolved
      | None ->
        (* No resolution found.  When the constructor-expression flag is set,
           all promoted vars become [Tany] (= std::any) because module-level
           type aliases are always std::any and non-Type promoted vars (like
           [base_category]) have no alias at all.  Otherwise keep the marker
           for concept generation and signature printing. *)
        if (!tctx).in_constructor_expr then Any
        else Promoted_member var_id )
    | None -> Any )
  | Tglob (g, _, _) when Table.is_value_dep_type_scheme g ->
    (* Value-dependent type scheme (e.g. [sym_semty : sym -> Type]) applied to a
       runtime value — not representable as a C++ type, so erase to [std::any].
       This keeps erasure consistent: such values are already stored as
       [std::any], so the types that mention them are [std::any] too, and no
       [any_cast] guard is needed at use sites. *)
    Any
  | Tglob (g, ts, args) when is_custom g ->
    Entity_application
      ( g,
        List.map (cpp_ir_of_ml_type env ~ns tvars) ts,
        List.map (fun a -> !type_term_arg env a) args )
  | Tglob (g, ts, _) ->
    (* For inductives, only keep type args that correspond to parameters (not
       indices). Parameters become template params in C++; indices are
       erased. *)
    let filtered_ts =
      match g with
      | GlobRef.IndRef (kn, _) ->
        (* Filter type args to keep only parameters (not indices). Use
           get_ind_num_param_vars_opt to determine how many to keep. For
           local/self-references with non-empty tvars, we can use tvars length
           as a fallback, but prefer the table lookup for accuracy. *)
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars ->
          (* Only keep the first num_param_vars type args - the rest are
             indices *)
          safe_firstn num_param_vars ts
        | None ->
          (* Fallback: if tvars is non-empty and this is a local reference, use
             tvars length *)
          let is_local = Ref.User.Set.mem g ns || spells_bare g in
          if is_local && tvars <> [] then
            safe_firstn (List.length tvars) ts
          else
            ts )
        (* Keep all if we can't determine *)
      | _ -> ts
    in
    (* Only propagate ns into type arguments when g itself is a self-ref.
       For non-self types (e.g. list inside tree's definition), type args
       stay bare — the field-level wrapping handles the cycle-breaking.
       This ensures type variables are never shared_ptr-wrapped at instantiation. *)
    let ns_for_args =
      if Ref.User.Set.mem g ns then ns else Ref.User.Set.empty
    in
    let converted_ts =
      List.map (cpp_ir_of_ml_type env ~ns:ns_for_args tvars) filtered_ts
    in
    let converted_ts =
      match g with
      (* Only where a later parameter's type mentions an earlier one --
         [sigT A (P : A -> Type)] -- does erasing the earlier one erase the
         later.  An erased family ([tree void1 R], [void1] logical) is
         nothing [R] depends on. *)
      | GlobRef.IndRef _ when Table.has_dependent_params g ->
        let rec first_ktype_idx i = function
          | [] -> max_int
          | (Tdummy Ktype | Tmeta {contents = Some (Tdummy Ktype)}) :: _ -> i
          | _ :: rest -> first_ktype_idx (i + 1) rest
        in
        let cutoff = first_ktype_idx 0 filtered_ts in
        if cutoff < max_int then
          List.mapi
            (fun i t -> if i > cutoff then index_erase_type_ir t else t)
            converted_ts
        else
          converted_ts
      | _ -> converted_ts
    in
    let converted_ts = apply_hkt_tyctors_ir g converted_ts in
    let converted_ts = ind_promoted_type_args_ir g @ converted_ts in
    let core : Cpp_ir.Lowered.Type.t = Entity_application (g, converted_ts, []) in
    ( match g with
    | GlobRef.IndRef _ ->
      (* Enum inductives are value types - no shared_ptr wrapping *)
      if is_enum_inductive g then
        let is_local = Ref.User.Set.mem g ns || spells_bare g in
        if is_local then
          core
        else
          In_namespace (g, core)
      else
        (* Check if this inductive is in the explicit ns list or in
           local_inductives context *)
        let is_self_ref = Ref.User.Set.mem g ns in
        (* Check if g is a mutual sibling: shares the same MutInd.t KerName
           as any member of ns, but at a different index. Mutual siblings
           need shared_ptr because their types are incomplete (forward-declared). *)
        let is_mutual_sibling =
          (not is_self_ref) &&
          match g with
          | GlobRef.IndRef (kn_g, _) ->
            Ref.User.Set.exists (fun r ->
              match r with
              | GlobRef.IndRef (kn_r, _) ->
                MutInd.CanOrd.equal kn_g kn_r
              | _ -> false) ns
          | _ -> false
        in
        let is_local = is_self_ref || spells_bare g in
        let is_uniform_self_ref =
          if not is_self_ref then
            true
          else if converted_ts = [] then
            (* Non-parametric inductive: self-reference is trivially uniform.
               The surrounding context may have type vars (e.g. T1 in rect<T1>)
               that are unrelated to the inductive's own parameters — don't
               let those force shared_ptr for a monomorphic self-reference. *)
            true
          else
            List.length converted_ts = List.length tvars
            && List.for_all2
                 (fun ty id ->
                   match (ty : Cpp_ir.Lowered.Type.t) with
                   | Variable (Index (_, Some id') | Named id') -> Id.equal id id'
                   | _ -> false)
                 converted_ts
                 tvars
        in
        if
          (is_self_ref || is_mutual_sibling)
          && not (Table.is_coinductive g)
          && is_uniform_self_ref
        then
          (* Recursive value-type self/mutual references are owned by their
             containing constructor. The pointed-to type may be incomplete at
             field declaration time, so it still needs indirection, but unique
             ownership plus explicit clone is enough. (Arena mode rewrites this
             shared_ptr to a raw arena pointer at the field-declaration site in
             gen_decls, so that method return/parameter positions are unaffected.) *)
          Shared_pointer core
        else if (is_self_ref || is_mutual_sibling) && Table.is_coinductive g
        then
          (* A coinductive value is already a handle on one shared node, so
             a field holding one holds it by value.  The constructor struct
             that holds it is a member template, completed only once the
             coinductive is -- see [Fdeferred_struct]. *)
          core
        else if is_self_ref || is_mutual_sibling then
          (* Non-uniform recursion uses shared_ptr rather than unique_ptr
             because destructor instantiation would diverge. *)
          Shared_pointer core
        else if is_local then
          (* Local non-self inductive: value type, no pointer wrapping *)
          core
        else if not (get_record_fields g == []) then
          (* Record inductive: value type, no pointer wrapping *)
          core
        else
          (* External inductive: value type, namespace-qualified *)
          In_namespace (g, core)
    | _ -> core )
  | Miniml.Tvar (_, i) -> Variable (Index (i, tvar_name_at tvars i))
  (* A higher-kinded variable applied to arguments.  The head stays a type
     variable here; [Gen_decls.apply_hkt_resolutions] rewrites it to the
     instance's associated type, leaving [Tapply] to render the application. *)
  | Tapp (i, args) ->
    let head : Cpp_ir.Lowered.Type.t = Variable (Index (i, tvar_name_at tvars i)) in
    Apply (head, List.map (cpp_ir_of_ml_type env ~ns tvars) args)
  | Tmeta {contents = Some t} -> cpp_ir_of_ml_type env ~ns tvars t
  | Tmeta {contents = None} | Topen _ ->
    (* Unresolved meta - use std::any for type erasure. This happens for
       existential type variables in indexed inductives. *)
    Any
  (* Tdummy marks erased type/prop/implicit parameters in the ML AST. We convert
     them to Tglob(VarRef "dummy_*") as intermediate markers so that downstream
     filtering (is_cpp_dummy_type / prints_as_any / filter_erased_type_args in
     gen_expr, eta_fun, and gen_decl_for_pp) can detect and drop them. These
     markers should never survive to the C++ output — the filtering pipeline
     removes them from template argument lists and function signatures. *)
  | Tdummy Ktype -> Erased Type
  | Tdummy Kprop -> Erased Proof
  | Tdummy (Kimplicit _) -> Erased Implicit
  | Tstring ->
    External ("std::string", [])
  (* Extraction gave up naming this type.  It prints as [std::any], but we
     know nothing about how the value is actually represented. *)
  | Tunknown -> Obligation Opaque_type
  (* A hole is ordinary data inside an instantiation, and a reader resolves
     it, leaves the parameter to deduction, or declines before converting:
     one reaching a C++ type is a reader that did none of these. *)
  | Thole hole ->
    Probe.violation "inference hole"
      Pp.(str "hole _" ++ int hole ++ str " reached a C++ type");
    Obligation Opaque_type
  | Taxiom -> Entity_application (GlobRef.VarRef (Id.of_string "axiom"), [], [])

(** Convert ML type arguments to C++ template parameters, applying type
    simplification and handling out-of-scope type variables.

    This function maps a list of ML types to C++ types for use in template
    argument lists. It performs two key transformations:

    1. Type simplification via [type_simpl] to normalize ML types
    2. Conversion to C++ types via [convert_ml_type_to_cpp_type]
    3. Detection and erasure of unbound type variables

    The [tvars] parameter specifies the type variables in scope (as a list of
    typename declarations in the current C++ context). When a [Tvar] appears
    with [None] for its binding and [tvars] is non-empty, this indicates the
    type variable index is out of scope — it references a typename that doesn't
    exist in the current C++ context.

    Out-of-scope type variables are marked as [dummy_type], which triggers
    [filter_erased_type_args] to drop the entire type argument list. This is
    safer than emitting invalid C++ like [template<typename T> ... U] where
    [U] is undefined.

    Example scenario where this occurs:
    - ML function with type scheme [forall A B, A -> B -> option A]
    - Partial application instantiates [A] but leaves [B] polymorphic
    - C++ code generator enters context with only [typename A]
    - Type arg list includes [Tvar 2] for [B]
    - [convert_ml_type_to_cpp_type] returns [Tvar(2, None)] (no binding)
    - We mark it [dummy_type] to trigger erasure

    @param env   Translation environment (unused in current implementation)
    @param tvars Type variables in scope (C++ typename parameters)
    @param tys   ML type arguments to convert
    @return List of C++ types, with out-of-scope Tvars marked as dummy_type *)

(** Whether a bare reference to global [x] must be spelled [x()]: it is
    declared as a zero-parameter function rather than a data member.  That is
    the case for thunked values (monadic definitions, cofixpoints, extracted
    axioms) and for definitions that really do take C++ parameters.

    An ML arrow is {i not} enough: a definition all of whose arguments are
    erased (a lemma-only argument, say) converts to a non-function C++ type
    and is emitted as a data member by {!Gen_decls.gen_spec}.  Asking the
    converter is what keeps the two in step. *)
let glob_is_nullary_function x =
  match callee_ml_type x with
  | None -> false
  | Some ml_ty ->
    thunk_reason x <> None
    || ( match cpp_ir_of_ml_type (empty_env ()) [] ml_ty with
       | Function _ -> true
       | _ -> false )

(** The global [x], spelled [cglob], applied to [args]: a call, except that a
    global value referenced bare stays a value ({!glob_is_nullary_function}). *)
let apply_global x (cglob : Cpp_ir.Lowered.Expr.t) args =
  if args = [] && not (glob_is_nullary_function x) then cglob else Cpp_ir.Build.call cglob args

(** [resolves_to_any_type ty] — true if [ty] ultimately resolves to
    [std::any].  Handles direct [Tany], erased-type constants (aliases for
    [std::any] registered via {!Table.is_erased_type_const}), and type
    aliases that expand to an erased type.  Used to decide whether a
    scrutinee's template argument makes a constructor field store its
    value as [std::any] at runtime. *)
let rec resolves_to_any_type_ir : Cpp_ir.Lowered.Type.t -> bool = function
  | Any | Obligation Opaque_type -> true
  | Erased _ -> false
  | Entity_application (g, [], _) when Table.is_erased_type_const g -> true
  | Entity_application (g, [], _) ->
    let via_ml_ty =
      match find_type_opt g with
      | Some ml_ty ->
        let tvars = get_current_type_vars () in
        Some (cpp_ir_of_ml_type (empty_env ()) tvars ml_ty)
      | None ->
        (match g with
         | GlobRef.ConstRef kn ->
           (match Table.lookup_typedef_unchecked kn with
            | Some ml_ty ->
              let tvars = get_current_type_vars () in
              Some (cpp_ir_of_ml_type (empty_env ()) tvars ml_ty)
            | None -> None)
         | _ -> None)
    in
    (match via_ml_ty with
     | Some cvt -> resolves_to_any_type_ir cvt
     | None -> false)
  | t when Cpp_ir.Types.prints_as_any t -> true
  | _ -> false

(** How a slot of C++ type [t] already known to be boxed boxes its value
    ({!slot_repr_of_cpp_type_ir}). *)
let box_kind_of_cpp_type_ir t = if names_erased_alias_ir t then Family_box else Var_box

(** The representation a value takes in a slot of C++ type [t]: the one
    classifier a slot's {!Ml_type_util.slot_repr} is decided by.  A type that
    resolves to [std::any] is boxed, as a [Family_box] where it names a
    declaration whose body erased, spelled through its alias -- a
    value-indexed family -- and as a [Var_box] otherwise
    ({!box_kind_of_cpp_type_ir}, for a slot already known to be boxed). *)
let slot_repr_of_cpp_type_ir t =
  if resolves_to_any_type_ir t then Boxed (box_kind_of_cpp_type_ir t) else Native

(** [cpp_of_ml_ir env t] converts an ML type in the type-variable scope that is
    currently in effect.  Nearly every conversion inside expression generation
    wants this, and spelling out {!get_current_type_vars} at each one invites
    passing the wrong scope. *)
let cpp_of_ml_ir env t = cpp_ir_of_ml_type env (get_current_type_vars ()) t

(** [template_arg_of_ml_type_ir ~site env tvars ty] converts [ty] for a template
    argument position, its arrows spelled as [site] says
    ({!Minicpp.arrow_site}).

    [Declared] for an argument that instantiates an {e inductive}'s
    parameter.  Such a parameter only names the type of a stored value, and the
    value is spelled at the flat arity {!cpp_ir_of_ml_type} gives the
    declaration; currying it would make the instantiation disagree with the
    type the declaration writes.  [Through_tvar] for a {e function}'s type
    parameter: the signature may mention it inside an arrow it writes out
    itself (as [ap : F (A -> B) -> ...] does), and there the currying is what
    makes the argument match. *)
let template_arg_of_ml_type_ir ~site env tvars ty =
  (* Template params emitted at expression/function-call sites are public API
     types. Recursive storage wrapping is introduced only when converting
     constructor fields with an explicit storage namespace. *)
  Cpp_ir.Types.spell_arrows site (cpp_ir_of_ml_type env ~ns:Ref.User.Set.empty tvars (type_simpl ty))

(** The site a callee's {e result} is spelled at ({!Minicpp.arrow_site}): a
    codomain that is a type variable takes its C++ shape from the template
    argument instantiating it, so it is curried; one the declaration writes
    out is flat there. *)
let codomain_site ml_ty = if ml_codomain_is_tvar ml_ty then Through_tvar else Declared

(** {!codomain_site} for a call to the global [id].  An inline custom
    constant has no template argument: what it yields is whatever its text
    reads -- [fst]'s [%a0.first] is the pair's component, stored flat. *)
let call_result_site id =
  if is_inline_custom id then Declared
  else match find_type_opt id with Some ml_ty -> codomain_site ml_ty | None -> Declared

let build_template_params_ir ~site env tvars tys =
  List.map
    (fun ty ->
      let t = template_arg_of_ml_type_ir ~site env tvars ty in
      (* Check for unbound type variables *)
      match t with
      | Variable (Index (_, None)) when tvars <> [] ->
        (* Type variable has no binding, but we're in a context with typename
           params. This means the Tvar index exceeds the scope of tvars.
           Mark as dummy_type to trigger full erasure via filter_erased_type_args.
           Using the unbound Tvar would generate invalid C++ references. *)
        (Erased Type : Cpp_ir.Lowered.Type.t)
      | _ ->
        (* Type is either bound, or we're in an untyped context (tvars = []).
           Keep the type as-is. *)
        t )
    tys

(** Generate code for a custom-extracted constructor application.

    Custom-extracted constructors have user-defined C++ syntax (registered via
    [Crane Extract Constant]) that may include type argument placeholders like
    [%t0], [%t1], etc. This function builds the C++ expression by:
    1. Filtering the ML type argument list to keep only type parameters
       (dropping index arguments that don't correspond to C++ template params)
    2. Converting ML types to C++ types via [build_template_params]
    3. Filtering erased types (Tdummy Ktype → dummy_type) to avoid passing
       empty or partial template argument lists to custom syntax
    4. Wrapping in [mk_cppglob] to apply the custom syntax template

    The filtering is critical because custom syntax strings expect concrete
    type arguments for their placeholders. If we pass an empty or erased
    type arg list, the custom syntax renderer in cpp_print.ml will raise
    an anomaly ("Custom syntax: unbound type argument").

    Example:
    - ML: [MLcons(Tglob(option, [Tglob(nat)]), cons_ctor, [5])]
    - Custom syntax: [(Datatypes.option, 0) := "std::optional<%t0>"]
    - After filtering: [std::optional<unsigned int>]
    - Generated C++: [std::make_optional<unsigned int>(5u)]

    Note: This only handles custom constructors. Regular (non-custom) inductives
    follow a different code path via the main [gen_expr] MLcons case.

    @param env Translation environment (contains type context)
    @param ty  ML type of the constructor application (contains type args)
    @param r   Constructor reference (must be custom-extracted)
    @param ts  ML expression arguments (converted to C++ recursively)
    @return C++ expression applying custom syntax with type/value arguments *)

(** [template_params_of_ml ~site:Through_tvar env tys] is {!build_template_params_ir} against the
    type variables the enclosing scope has in hand; see {!cpp_of_ml_ir}. *)
let template_params_of_ml_ir ~site env tys = build_template_params_ir ~site env (get_current_type_vars ()) tys

(** [param_expected_cpp_ty env param_tys i] is the C++ type the callee declares
    for its [i]th parameter, and so the type an argument generated for that
    position should aim at.  [None] when the position says nothing useful:
    either the callee has fewer parameters, or the declared type is erased and
    naming [std::any] as the expectation would only invite a spurious box. *)
let param_expected_cpp_ty_ir env param_tys i =
  match List.nth_opt param_tys i with
  | Some ml_ty ->
    let cpp_ty = cpp_of_ml_ir env ml_ty in
    if Cpp_ir.Types.prints_as_any cpp_ty then None else Some cpp_ty
  | None -> None

(** [ml_erases_to_box env t] -- whether [t] is represented as a [std::any]
    here.  Conversion is what answers this: a value-dependent type such as
    [syms_semty xs], or a type variable this scope leaves unresolved, is only
    revealed as a box once converted, and a [Type]-valued definition hides one
    behind a [using] alias that {!resolves_to_any_type} follows. *)
let ml_erases_to_box env t = resolves_to_any_type_ir (cpp_of_ml_ir env t)

(** [result_cpp_via_receiver env callee_ty args] is the C++ type a call's
    result really has, where the callee's declared codomain is one of the type
    variables its first argument's type instantiates -- the field a projection
    out of a dependent pair hands back, say.

    The answer is read off the {e converted} receiver, at the template position
    the codomain occupies in it.  Converting the codomain's own instantiation
    instead is not the same thing: a type argument that the receiver's
    conversion erases still spells concretely in isolation, and the field it
    describes is then physically a [std::any] while its ML type denies it.
    [None] means the call is not of this shape, or that the two spellings of
    the receiver disagree on how many arguments it has -- the position would
    then name the wrong one. *)
let result_cpp_via_receiver_ir env callee_ty args : Cpp_ir.Lowered.Type.t option =
  let var_index t = match resolve_tmeta t with Miniml.Tvar (_, j) -> Some j | _ -> None in
  let position_of j formals =
    let rec find i = function
      | [] -> None
      | f :: rest -> if var_index f = Some j then Some i else find (i + 1) rest
    in
    find 0 formals
  in
  (* {!Ml_type_util.template_args} in CppIR. *)
  let rec template_args_ir t =
    match unqualify_ty_ir t with
    | Reference (_, t) | Pointer t | Shared_pointer t -> template_args_ir t
    | Entity_application (_, args, _) | Named (_, args) | External (_, args) | Apply (_, args) -> Some args
    | _ -> None
  in
  match (var_index (ml_codomain callee_ty), ml_value_domains callee_ty, args) with
  | Some j, dom0 :: _, arg :: _ -> (
    match (resolve_tmeta dom0, Option.map resolve_tmeta (infer_ml_body_type arg)) with
    | Miniml.Tglob (g1, formals, _), Some (Miniml.Tglob (g2, actuals, _) as recv)
      when Common.globref_equal g1 g2 -> (
      match (position_of j formals, template_args_ir (cpp_of_ml_ir env recv)) with
      | Some i, Some cpp_args when List.length actuals = List.length cpp_args ->
        List.nth_opt cpp_args i
      | _ -> None )
    | _ -> None )
  | _ -> None

(** [iife_void_return env typ pv] is [Some Tvoid] when the match's branches
    produce nothing: a lambda that may fall off its end has to say [-> void]
    explicitly. *)
let iife_void_return_ir env typ pv : Cpp_ir.Lowered.Type.t option =
  let branch_rty =
    match Array.to_list pv with (_, rty, _, _) :: _ -> rty | [] -> typ
  in
  let r = cpp_of_ml_ir env branch_rty in
  if is_cpp_unit_type_ir r || ml_type_is_void_call branch_rty then
    Some Void
  else None

(** [iife_closure_return env typ pv stmts] is the return type to annotate the
    IIFE wrapping a match with, given the branches already generated.

    Distinct closures have no common type, so a match that returns one from
    some branch needs the [std::function] they all convert to.  Otherwise
    [None]: deducing beats annotating, because the branch's recorded ML type
    can outlive the term it described -- a motive's arrow surviving the
    application that consumed it -- and because it may still mention type
    variables that mean nothing in a non-template context.

    The question is asked of the generated statements, not of the ML terms: a
    branch spells a closure whether it was written as a lambda, arose from a
    partial application, or is a function-typed binder handed straight back,
    and only the C++ says which.  A binder counts because a function-typed
    parameter is a deduced template parameter of its own -- [f] and [g] of the
    same Rocq type are still two C++ types, and two branches returning one
    each deduce nothing. *)
let iife_closure_return_ir env typ pv (stmts : Cpp_ir.Lowered.Stmt.t list) : Cpp_ir.Lowered.Type.t option =
  let found = ref false in
  let rec is_arrow = function
    | Miniml.Tarr _ -> true
    | Miniml.Tmeta {contents = Some t} -> is_arrow t
    | _ -> false
  in
  let binder_is_fun id =
    match env_type_of_id id with
    | Some ty -> is_arrow ty
    | None -> false
  in
  let scan_expr (e : Cpp_ir.Lowered.Expr.t) =
    match e with
    | Lambda _ -> found := true
    | Local id when binder_is_fun id -> found := true
    | _ -> ()
  in
  let rec scan_stmt (s : Cpp_ir.Lowered.Stmt.t) =
    match s with
    | Return (Some e) -> scan_expr e
    | _ ->
      Cpp_ir.Subterms.stmt
        ~expr:(fun _ -> ())
        ~stmts:(List.iter scan_stmt) s
  in
  List.iter scan_stmt stmts;
  if not !found then None
  else
    let branch_rty =
      match Array.to_list pv with (_, rty, _, _) :: _ -> rty | [] -> typ
    in
    match cpp_of_ml_ir env branch_rty with Function _ as r -> Some r | _ -> None

(** [glob_declared_cod_erases r] -- whether the declaration of [r] returns a
    box.  A declaration is converted from the global's own ML type with no
    type variables in scope, and that conversion erases a result no parameter
    pins down -- a type index, say -- however concrete the type is at a given
    call site.  So the question can only be asked of the whole type: the
    codomain alone converts to the type variable and reveals nothing. *)
let glob_declared_cod_erases r =
  match callee_ml_type r with
  | Some ty -> (
    match cpp_ir_of_ml_type (empty_env ()) [] (type_simpl ty) with
    | Function (_, cod) -> Cpp_ir.Types.prints_as_any cod
    | _ -> false )
  | None -> false

(** Record the C++ type of the pattern variable at de Bruijn index [i].

    A box is never overwritten by a concrete type.  Several passes describe
    the same binder -- an outer erased pair match says every field is a
    [std::any], and the per-field pass then reports the definition-site type
    the scrutinee instantiates -- and the erased view is the one that
    describes the runtime value. *)
let record_binder_type i (t : Cpp_ir.Lowered.Type.t) =
  let boxed_by_pattern =
    match IntMap.find_opt i (!tctx).cpp_binder_types with
    | Some (Obligation Opaque_type, Bpattern) -> false
    | Some (t', Bpattern) -> resolves_to_any_type_ir t'
    | _ -> false
  in
  if not boxed_by_pattern then
    tctx :=
      { !tctx with
        cpp_binder_types = IntMap.add i (t, Bpattern) (!tctx).cpp_binder_types }

(** [pattern_field_pins ~scrut_pinned ~cname ~typ ~env ~n_fields
    ~non_erased_def_site_field_tys] -- what a pattern-match branch pins down
    about each of its [n_fields] fields, in field order: whether the field is
    stored as a box, and the scrutinee's template argument that fixes its
    C++ type, if its definition-site type is one of the inductive's own
    parameters.  Reads no binder: the scrutinee is described by its ML type
    and, where an enclosing branch pinned it, by that C++ type.

    @param scrut_pinned  the C++ type an enclosing branch pinned down for the
           scrutinee, when it is a local binder
    @param cname  constructor reference (to look up parameter count)
    @param typ    ML type of the scrutinee
    @param env    translation environment
    @param n_fields    number of pattern variables in the branch
    @param non_erased_def_site_field_tys  definition-site field types
           with erased (dummy) entries filtered out *)
let pattern_field_pins ~scrut_pinned ~cname ~typ ~env ~n_fields
    ~non_erased_def_site_field_tys =
  let scrut_cpp_ty =
    (* An enclosing branch may already have pinned the scrutinee's C++ type
       down -- [SigT<any, pair<any,any>>] tells us its payload binder is a
       [pair<any,any>], which its ML type (a bare type variable) does not.
       Prefer that over re-deriving from the ML type. *)
    match scrut_pinned with
    | Some t when not (resolves_to_any_type_ir t) -> t
    | _ ->
      cpp_of_ml_ir env typ
  in
  (* Whether a {!Minicpp.Topaque} among the scrutinee's template arguments is
     a box.  [Topaque] only admits that the argument could not be resolved --
     but for an inductive Crane generates, the field that names it is written
     out, and {!Cpp_erasure.materialise} spells that declaration [std::any], so
     the value really is boxed.  A custom-extracted scrutinee has no such
     declaration: [std::optional<T>] is spelled by the mapping, and where the
     scrutinee is only ever bound to [auto] nothing wrote a box at all. *)
  let opaque_arg_is_a_box =
    match resolve_tmeta typ with
    (* ... unless the mapping's own type argument is one that erases: a family
       indexed by a value is spelled [std::any] in the instantiation, so the
       [std::optional<std::any>] the mapping produced really does hold a
       box. *)
    | Miniml.Tglob (g, args, _) ->
      not (Table.is_custom g) || List.exists (ml_erases_to_box env) args
    | _ -> true
  in
  (* Whether one of the scrutinee's template arguments holds a boxed value.
     This is the only question asked about an argument's erasure here, so it
     is settled once: [Topaque] is the sole case where being spelled
     [std::any] does not settle it, and it is decided above rather than
     re-decided at each site. *)
  let arg_is_a_box (t : Cpp_ir.Lowered.Type.t) =
    match t with Obligation Opaque_type -> opaque_arg_is_a_box | t -> resolves_to_any_type_ir t
  in
  let scrut_template_args =
    let args = extract_template_args_ir scrut_cpp_ty in
    (* One boxed argument means the whole instantiation was erased, so every
       argument is boxed -- the same rule the type-index cutoff applies to a
       [Tdummy Ktype] index, here for an argument erased because it mentions a
       free (existential) type variable.  Without it a payload
       [pair<any, function<nat(any)>>] would be read back component-wise at
       two different erasures from the [pair<any, any>] its producer stored. *)
    (* An unresolved argument of a custom-extracted scrutinee does not count:
       see [opaque_arg_is_a_box]. *)
    if List.exists arg_is_a_box args then
      (* An argument that already carries an erased component is at the shape
         its producer stored it in -- a [pair<List<any>, any>] payload is
         written down that way in the field, and reading it back as a flat
         [any] would lose the components the producer boxed individually. *)
      List.map
        (fun a -> if has_tany_in_type_ir a then a else index_erase_type_ir a)
        args
    else args
  in
  let num_pv = Table.get_ctor_num_param_vars cname in
  (* The scrutinee's template argument that fixes this field's type, if the
     field's definition-site type is one of the inductive's own parameters.
     [Tapp (k, _)] counts: [sigT]'s payload field is written [P x], a
     parameter applied to the witness, and it is [P] that the instantiation
     pins down. *)
  let rec field_template_arg = function
    | Miniml.Tvar (_, k) | Miniml.Tapp (k, _) ->
      List.nth_opt scrut_template_args (k - 1)
    | Miniml.Tmeta {contents = Some t} -> field_template_arg t
    | _ -> None
  in
  let field_arg field_i =
    if num_pv = 0 then None
    else Option.bind (List.nth_opt non_erased_def_site_field_tys field_i)
           field_template_arg
  in
  let is_field_stored_as_any field_i =
    if num_pv = 0 then
      match List.nth_opt non_erased_def_site_field_tys field_i with
      | Some def_ty ->
        let cpp_ty =
          cpp_ir_of_ml_type (empty_env ()) ~ns:Ref.User.Set.empty [] def_ty
        in
        has_unnamed_tvar_ir cpp_ty
      | None -> false
    else
      match field_arg field_i with
      | Some t -> arg_is_a_box t
      | None -> false
  in
  List.init n_fields (fun field_i -> (is_field_stored_as_any field_i, field_arg field_i))

(** [populate_erased_field_env ?scrut_db ...] records {!pattern_field_pins}
    in {!cpp_binder_types} for a branch binding [n_pat_vars] pattern
    variables: a field stored as a box is recorded erased, then the template
    argument fixing a field's type, which does not overwrite the box.
    [scrut_db] is the scrutinee's de Bruijn index within the branch, when it
    is a local binder whose C++ type an enclosing branch recorded. *)
let populate_erased_field_env ?scrut_db ~cname ~typ ~env ~n_pat_vars ~n_fields
    ~non_erased_def_site_field_tys () =
  let scrut_pinned = Option.bind scrut_db pattern_binder_type in
  List.iteri
    (fun field_i (stored_as_any, arg) ->
      let db_idx = n_pat_vars - field_i in
      if stored_as_any then record_binder_type db_idx Any;
      Option.iter (record_binder_type db_idx) arg )
    (pattern_field_pins ~scrut_pinned ~cname ~typ ~env ~n_fields ~non_erased_def_site_field_tys)

(** [match_scrutinee_type env typ t pv ~var_type ~var_cpp_type] -- the type a
    match over [t] annotated [typ], with branches [pv], is generated at: the
    annotation, with what it leaves open filled from the scrutinee -- a
    variable's binder ([var_type] its ML type, [var_cpp_type] the C++ type
    it was decided to have), anything else its own structure -- and, failing
    an inductive, the one the first branch's constructor belongs to.  Reads
    no binder itself: what a variable stands for is the caller's to say. *)
let match_scrutinee_type env (typ : ml_type) t pv ~var_type ~var_cpp_type =
  (* When the match type annotation has unresolved Tvars, try to resolve from
     context. This handles monomorphic functions where MLcase has Tvar but the
     concrete type is known. *)
  let rec resolvable_here = function
    | Miniml.Tglob (g, ts, _) ->
      ( (not (Table.is_promoted_type_var g))
      || promoted_var_resolution g <> None )
      && List.for_all resolvable_here ts
    | Miniml.Tarr (a, b) -> resolvable_here a && resolvable_here b
    | Miniml.Tmeta {contents = Some t} -> resolvable_here t
    | _ -> true
  in
  let resolve_tvar_type typ candidate =
    match (typ, candidate) with
    | Miniml.Tglob (r1, _, _), Miniml.Tglob (r2, _, _)
      when globref_equal r1 r2
           && has_tvar typ
           && (not (has_tvar candidate))
           (* Only a candidate that erased nothing replaces the annotation
              whole: [observe t] at a family its call erased is [itreeF D _]
              where the annotation knows the family. *)
           && not (ml_type_contains_erased candidate) -> candidate
    | _ ->
      (* The annotation may state the inductive and leave its argument open --
         [EOU _] for a call whose declared result is [EOU ptr] -- and then the
         match spells [std::any] where the value has a type.  The candidate is
         the declaration the scrutinee was produced by, so it may fill what the
         annotation left open, and nothing more: see
         {!Ml_type_util.refine_erased}.  A promoted variable this scope cannot
         resolve is not an answer, and neither is an erased one. *)
      Ml_type_util.refine_erased
        ~writable:(fun t ->
          resolvable_here t
          && names_only_scoped_tvars_ir (cpp_of_ml_ir env t)
          && not (Ml_type_util.has_tany_in_type_ir (cpp_of_ml_ir env t)) )
        typ candidate
  in
  let typ =
    match t with
    | MLrel (i, _) | MLmagic (_, MLrel (i, _), _) ->
      (* Scrutinee is a variable reference — use its concrete type, the one
         its binder was given, a parameter's as much as a let's.  Unwrap Tmeta
         wrappers since env_types may store types in Tmeta form. *)
      let rec unwrap_tmeta = function
        | Miniml.Tmeta {contents = Some t} -> unwrap_tmeta t
        | t -> t
      in
      let env_ty_opt =
        try
          let env_ty =
            unwrap_tmeta (match var_type i with Some t -> t | None -> raise Not_found)
          in
          match env_ty with
          | Miniml.Tglob _ -> Some env_ty
          | _ -> None
        with _ -> None
      in
      let typ =
        match env_ty_opt with
        | Some let_ty -> resolve_tvar_type typ let_ty
        | None -> typ
      in
      (* The variable's declared C++ type is what its value is: where it
         erased a position -- a pattern field of a plain family parameter,
         [Sum1<BE, cE, std::any>] inside [Sum1<AE, _, X>], whose ML type
         says [X] -- the match spells it erased too. *)
      let rec erase_as ml (cpp : Cpp_ir.Lowered.Type.t) =
        match (resolve_tmeta ml, Ml_type_util.unqualify_ty_ir cpp) with
        | Miniml.Tglob (g, mas, x), Entity_application (g', cas, _)
          when GlobRef.CanOrd.equal g g' && List.length mas = List.length cas ->
          Miniml.Tglob
            ( g,
              List.map2
                (fun m c ->
                  if Cpp_ir.Types.prints_as_any c && not (ml_type_contains_erased m) then
                    Miniml.Tunknown
                  else erase_as m c )
                mas cas,
              x )
        | m, _ -> m
      in
      ( match var_cpp_type i with
      | Some bt -> erase_as typ (strip_cpp_ref_const_ir bt)
      | None -> typ )
    | _ ->
      (* Anything else: the scrutinee's own structure says what it produces,
         through the one reader -- a call's instantiated codomain, a
         projection's field type.  Reading it here rather than re-deriving a
         callee's return type keeps a projection, which is an [MLcase] and not
         an application at all, from being left out. *)
      ( match
          ( match ml_projection_field_type (strip_magic t) with
          | Some _ as c -> c
          | None -> infer_ml_body_type t )
        with
      | Some cand -> resolve_tvar_type typ cand
      | None -> typ )
  in
  (* When the type is still unresolved (Tunresolved / Tdummy / non-Tglob),
     recover the inductive from the first branch's constructor pattern -- a
     constructor determines the inductive it belongs to, so this is sound
     wherever the scrutinee's own type failed to resolve.  It happens for a
     dependent field stored as [std::any] (sigT's second projection) and for
     the body of an instance method, which is extracted against the class's
     erased carrier and so carries no type for the scrutinee at all. *)
  let typ =
    match typ with
    | Miniml.Tglob _ -> typ
    | _ ->
      ( try
          let _, _, pat0, _ = pv.(0) in
          match pat0 with
          | Pusual (GlobRef.ConstructRef (ip, _))
          | Pcons (GlobRef.ConstructRef (ip, _), _) ->
            Miniml.Tglob (GlobRef.IndRef ip, [], [])
          | _ -> typ
        with _ -> typ )
  in
  typ

(** Follow a name for a type through to the type it stands for.  A [using]
    alias hides the arguments its right-hand side was written with, and those
    arguments are exactly what a value built into such a slot has to agree
    with.  Returns the type unchanged when it is not an alias. *)
let rec unfold_cpp_typedef_ir env (cpp_ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  match cpp_ty with
  | In_namespace (_, inner) -> unfold_cpp_typedef_ir env inner
  | Entity_application (GlobRef.ConstRef kn, args, _) -> (
    match Table.lookup_typedef_unchecked kn with
    | Some ml_ty ->
      let body = cpp_of_ml_ir env ml_ty in
      let n_promoted =
        let n = List.length (Table.promoted_type_params (GlobRef.ConstRef kn)) in
        if List.length args >= n + Mlutil.type_maxvar ml_ty then n else 0
      in
      if args = [] then body
      else Cpp_ir.Types.substitute (fun i -> if i >= 1 then List.nth_opt args (n_promoted + i - 1) else None) body
    | None -> cpp_ty )
  | _ -> cpp_ty

(** Whether the pattern variable at de Bruijn index [i] holds a box, and so
    must be recovered with an [any_cast] before it is used at a concrete
    type.  Read off the recorded type rather than tracked alongside it: a
    binder is boxed exactly when the scrutinee's instantiation erased its
    field. *)
let binder_is_boxed i =
  (* [Topaque] prints as [std::any] but admits only that the representation is
     unknown here; nothing may be unboxed on the strength of it.  The
     distinction is {!coerce}'s, and a binder's answer has to draw it too. *)
  match binder_cpp_type i with
  | Some (Obligation Opaque_type) | None -> false
  | Some t -> resolves_to_any_type_ir t

(* How a binder kind is named in probe output. *)
let binder_kind_name = function
  | Kouter -> "outer"
  | Kparameter -> "parameter"
  | Klet -> "let"
  | Kfix -> "fix"
  | Kpattern -> "pattern"

(** [read_is_boxed i occ] -- whether the variable read at [occ], of the
    binder at de Bruijn index [i], holds a box: the answer the region's
    representation plan ({!Representation_plan.region}) gives for [occ],
    which plans every read of every region.  A read it has no answer for is
    an anomaly.  Under [CRANE_CHECK_IR] the answer is held to
    {!binder_is_boxed}, the one read off the binder's recorded C++ type. *)
let read_is_boxed i occ =
  let live () = binder_is_boxed i in
  let describe live planned =
    Pp.(
      str "a read"
      ++ (match (!tctx).body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
      ++ str ": lowering "
      ++ str (if live then "boxes" else "does not box")
      ++ str " its binder, the plan " ++ str planned)
  in
  match List.assq_opt occ (!tctx).planned_reads with
  | Some {rd_boxed; rd_kind} ->
    ( if Probe.checking () then
        let live = live () in
        let agrees = rd_boxed = live in
        Probe.hit "repr-read" (fun () ->
            (if agrees then "agree " else "disagree ")
            ^ binder_kind_name rd_kind
            ^ if live then " live-boxed" else " live-value");
        if not agrees then
          Probe.violation "variable read representation"
            (describe live ((if rd_boxed then "boxes" else "does not") ^ " (" ^ binder_kind_name rd_kind ^ ")")) );
    rd_boxed
  | None ->
    CErrors.anomaly
      Pp.(
        str "a read of " ++ int i
        ++ (match (!tctx).body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
        ++ str " is in no representation plan of the region it is lowered in")

(** [planned_binder_type ~use ~agree i occ] -- the C++ type the region's
    representation plan ({!Representation_plan.region}) gives the binder of
    the variable [i] read at [occ], where it plans one.  Under
    [CRANE_CHECK_IR] held to the type lowering recorded for the binder
    ({!binder_cpp_type}) through [agree], which says whether the two give
    the decision [use] names the same answer.  A read the plan has no answer
    for is an anomaly. *)
(* A C++ type, written compactly for a probe or a violation report. *)
let rec type_shape_ir : Cpp_ir.Lowered.Type.t -> string = function
  | Function (dom, cod) -> "fn(" ^ String.concat "," (List.map type_shape_ir dom) ^ ")->" ^ type_shape_ir cod
  | Any -> "any"
  | Auto -> "auto"
  | Obligation Opaque_type -> "opaque"
  | Const t -> "const " ^ type_shape_ir t
  | Reference (_, t) -> "ref " ^ type_shape_ir t
  | Entity_application (g, args, _) -> Pp.string_of_ppcmds (GlobRef.print g) ^ "<" ^ String.concat "," (List.map type_shape_ir args) ^ ">"
  | Variable (Index (i, Some id)) -> "T" ^ string_of_int i ^ ":" ^ Id.to_string id
  | Variable (Index (i, None)) -> "T" ^ string_of_int i
  | Variable (Named id) -> "N:" ^ Id.to_string id
  | Shared_pointer t -> "sp " ^ type_shape_ir t
  | Variant _ -> "variant"
  | Member (t, id) -> type_shape_ir t ^ "::" ^ Id.to_string id
  | Named (id, args) -> "id:" ^ Id.to_string id ^ "<" ^ String.concat "," (List.map type_shape_ir args) ^ ">"
  | External (n, _) -> "ext:" ^ n
  | Promoted_member id -> "prom:" ^ Id.to_string id
  | Instance (id, _) -> "inst:" ^ Id.to_string id
  | Erased _ -> "erased"
  | Apply (h, args) -> "app(" ^ type_shape_ir h ^ ")<" ^ String.concat "," (List.map type_shape_ir args) ^ ">"
  | In_namespace (_, t) -> "ns " ^ type_shape_ir t
  | _ -> "other"

let planned_binder_type ~use ~agree i occ =
  let show = function Some t -> type_shape_ir t | None -> "none" in
  match List.assq_opt occ (!tctx).planned_reads with
  | Some {rd_type; rd_kind; _} ->
    ( if Probe.checking () then
        let live = binder_cpp_type i in
        let agrees = agree rd_type live in
        Probe.hit "repr-type" (fun () ->
            use ^ (if agrees then " agree " else " disagree ") ^ binder_kind_name rd_kind ^ " plan " ^ show rd_type
            ^ " live " ^ show live
            ^ (match (!tctx).body_owner with Some r -> " in " ^ Pp.string_of_ppcmds (GlobRef.print r) | None -> ""));
        if not agrees then
          Probe.violation "variable read binder type"
            Pp.(
              str "a read for " ++ str use
              ++ (match (!tctx).body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
              ++ str ": lowering's binder is " ++ str (show live) ++ str ", the plan's "
              ++ str (show rd_type)) );
    rd_type
  | None ->
    CErrors.anomaly
      Pp.(
        str "a read of " ++ int i
        ++ (match (!tctx).body_owner with Some r -> str " in " ++ GlobRef.print r | None -> mt ())
        ++ str " is in no representation plan of the region it is lowered in")

(** [planned_position occ ~live] -- the C++ type the position of the
    coercion at [occ] is generated against, as the region's position plan
    ({!Position_plan.region}) gives it, under [CRANE_CHECK_IR] held to
    [live], the type lowering threaded there.  A coercion the plan of the
    region it is lowered in does not reach is an anomaly. *)
let planned_position occ ~(live : Cpp_ir.Lowered.Type.t option) =
  let show = function Some t -> type_shape_ir t | None -> "none" in
  let owner () = match (!tctx).body_owner with Some r -> " in " ^ Pp.string_of_ppcmds (GlobRef.print r) | None -> "" in
  match List.find_opt (fun (o, _) -> Occurrence.equal o occ) (!tctx).planned_positions with
  | Some (_, planned) ->
    if Probe.checking () then begin
      let agrees = planned = live in
      Probe.hit "magic-pos" (fun () -> if agrees then "agree" else "disagree plan " ^ show planned ^ " live " ^ show live ^ owner ());
      if not agrees then
        Probe.violation "coercion position"
          Pp.(str ("a coercion" ^ owner () ^ " is lowered against " ^ show live ^ ", the plan's position is " ^ show planned))
    end;
    planned
  | None ->
    CErrors.anomaly Pp.(str ("a coercion" ^ owner () ^ " is in no position plan of the region it is lowered in"))

(** [reads_erased_pair_component env t] -- whether the coerced term [t]
    reads a component out of a pair recovered from a box, decided on Core:
    a global call whose one value argument is a coercion from a box planned
    at a product position, which lowering recovers at the erased shape
    [pair<any, any>] ({!boxed_shape_of_ir}).  Such a component is itself a
    box. *)
let reads_erased_pair_component env t =
  match t with
  | MLapp (MLglob _, args) -> (
    match List.filter (function MLdummy _ -> false | _ -> true) args with
    | [MLmagic (Mcoerce (from, _), _, occ)] -> (
      Cpp_ir.Types.prints_as_any (cpp_of_ml_ir env from)
      &&
      match List.find_opt (fun (o, _) -> Occurrence.equal o occ) (!tctx).planned_positions with
      | Some (_, Some (Cpp_ir.Type.Entity_application (g, _ :: _, _))) -> is_prod_global g
      | _ -> false )
    | _ -> false )
  | _ -> false

(** [t] with every type variable named by the default spelling of its
    index ({!Common.tvar_name}) written by the index alone: the two
    print the same, and lowering records a binder's type before its
    variables are named. *)
let default_tvar_names (t : Cpp_ir.Lowered.Type.t) =
  Cpp_ir.Types.map
    (fun (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
      match t with
      | Variable (Index (i, Some n)) when String.equal (Id.to_string n) (Common.tvar_name i) -> Variable (Index (i, None))
      | t -> t )
    t

(** [planned_binder_type_or_derive ~use ~agree env i occ] -- the
    planned C++ type of the binder of the variable [i] read at [occ]
    ({!planned_binder_type}), and failing one the conversion of its ML type
    under the current scope: an answer for every binder, where the plan
    deliberately has none for one at [Topaque], a dummy, or a conversion
    that failed.  Under [CRANE_CHECK_IR] the answer is held, through
    [agree], to the same derivation from the type lowering recorded for the
    binder ({!binder_cpp_type}). *)
let planned_binder_type_or_derive ~use ~agree env i occ =
  let derive = function Some _ as t -> t | None -> Option.map (cpp_of_ml_ir env) (get_env_type_opt i) in
  derive (planned_binder_type ~use ~agree:(fun p l -> agree (derive p) (derive l)) i occ)

(** Whether an application reads its result out of a value that carries
    erasure.

    An accessor's ML result type says nothing on its own: the second component
    of a dependent pair is a bare type variable whatever the pair holds.  What
    decides is the value being projected from -- a [SigT<std::any, std::any>]
    hands back a box, a [SigT<List<uint64_t>, List<uint64_t>>] hands back a
    list.  So the arguments are the evidence, and each is asked at whichever
    is the better authority on its C++ type: the type a variable's binder is
    planned at, or the term's own ML type. *)
let app_reads_erased_value env args =
  let carries t =
    Ml_type_util.has_erased_type_in_type_ir (unfold_cpp_typedef_ir env t)
  in
  (* A typeclass dictionary is not one of the values the result is read out
     of: it is how the call states its type arguments, and C++ resolves the
     result through it. *)
  let is_dictionary a =
    match infer_ml_body_type (strip_magic a) with
    | Some ty -> (
      match resolve_tmeta ty with
      | Miniml.Tglob (r, _, _) -> Table.is_typeclass r
      | _ -> false )
    | None -> false
  in
  List.exists
    (fun a ->
      if is_dictionary a then false
      else
      match strip_magic a with
      | MLrel (i, occ) -> (
        let carried = Option.map (fun t -> carries (strip_cpp_ref_const_ir t)) in
        match planned_binder_type_or_derive ~use:"erased argument" ~agree:(fun p l -> carried p = carried l) env i occ with
        | Some t -> carries (strip_cpp_ref_const_ir t)
        | None -> false )
      | a -> (
        match infer_ml_body_type a with
        | Some ty -> carries (cpp_of_ml_ir env ty)
        | None -> false ) )
    args

(** Record the C++ type of each of the [ids] most recently pushed binders,
    without pushing them again.  [?cpp] overrides the conversion for binders
    whose declared C++ type the caller has already computed; a declaration is
    always a better answer than re-deriving from the ML type, because it is
    what the emitted code actually says.  Call sites that only learn the
    declared types after pushing (a lambda decides [const auto &] for its
    erased parameters well after opening their scope) call this a second time
    to correct the assignment. *)
let assign_binder_types ?(cpp = []) env (ids : (Id.t * ml_type) list) =
  List.iteri
    (fun j (_, ml_ty) ->
      let assigned : Cpp_ir.Lowered.Type.t option =
        match List.nth_opt cpp j with
        | Some (Some t) -> Some (strip_param_wrappers t)
        | _ -> (try Some (cpp_of_ml_ir env ml_ty) with _ -> None)
      in
      match assigned with
      | Some t
        when t <> Obligation Opaque_type && not (is_cpp_dummy_type_ir t)
             && not (pinned_by_pattern (j + 1)) ->
        tctx :=
          { !tctx with
            cpp_binder_types =
              IntMap.add (j + 1) (t, Bbinding) (!tctx).cpp_binder_types }
      | _ -> ())
    ids

(** [push_binders env ids] is {!push_env_types} plus the C++ type assignment:
    each binder's C++ type is decided here, once, at the point it is bound,
    and recorded in {!Translation_state.cpp_binder_types}.

    This is the assignment that use sites are being migrated onto.  Today they
    re-derive a binder's C++ type wherever they need it, from whatever type
    variable scope happens to be in effect, so two uses of one binder can
    disagree about whether it holds a box -- which is what a [bad_any_cast]
    is.  Deciding at the binding site makes that disagreement unrepresentable.

    [?cpp] overrides the conversion for a binder whose type the caller already
    knows better than its ML type says, which is the case for pattern
    variables: it is the scrutinee's instantiation, not the field's
    definition-site type, that fixes those.  A [None] entry (or a short list)
    falls back to converting the ML type.

    The assignment records only types it actually knows.  A conversion that
    yields [Topaque] means the scope could not resolve the binder at all, and
    a dummy stands for a value that is not there; recording either would turn
    ignorance into the assertion "this binder holds a box", which is the one
    thing {!Minicpp.Topaque} exists to refuse.  Such binders keep no entry, so
    a reader still falls through to whatever it does today.  Conversion
    failures are skipped for the same reason, and so that a binder Crane
    cannot currently type does not become a new way for extraction to fail. *)
let push_binders ?(cpp = []) env (ids : (Id.t * ml_type) list) =
  push_env_types ids;
  assign_binder_types ~cpp env ids

(** [with_binders env ids f] runs [f] with [ids] (innermost first) pushed by
    {!push_binders}, and closes that scope however [f] leaves.

    It is the type half of a [push_vars'] that bound the same [ids] in the
    name environment: a body generated under the extended name environment
    reads its binders' types by de Bruijn index, so a name pushed without its
    type makes every lookup beneath it read the binder one further out. *)
let with_binders ?cpp env ids f =
  let saved = (!tctx).env_types in
  push_binders ?cpp env ids;
  Fun.protect ~finally:(fun () -> restore_env_types saved) f

(** [push_parameters env ids] is {!push_binders} for a declaration's
    parameters, whose class-typed ones are its dictionaries. *)
let push_parameters ?(cpp = []) env (ids : (Id.t * ml_type) list) =
  push_env_parameters ids;
  assign_binder_types ~cpp env ids

(** The type arguments the enclosing function's return type supplies for the
    inductive [ind], when it names [ind] with exactly [arity] of them.

    A constructor call for an inductive with dependent parameters has to
    instantiate the same template its caller expects, and the return type is
    where that expectation is recorded.  Namespace and [shared_ptr] wrappers
    are seen through, as are typedefs, which may name [ind] only indirectly.
    [None] when the return type says nothing about [ind]. *)
let expected_type_args_from_return_ir env ?slot ind ~arity =
  let rec go (cpp_ty : Cpp_ir.Lowered.Type.t) =
    match cpp_ty with
    | Entity_application (r, tys, _)
      when Names.GlobRef.CanOrd.equal ind r && List.length tys = arity ->
      Some tys
    | In_namespace (_, inner) | Shared_pointer inner -> go inner
    | Entity_application (_, tys, _) when List.exists (fun t -> go t <> None) tys ->
      List.find_map go tys
    | Entity_application (GlobRef.ConstRef kn, _, _) -> (
      match Table.lookup_typedef_unchecked kn with
      | Some ml_ty ->
        go (cpp_of_ml_ir env ml_ty)
      | None -> None )
    | _ -> None
  in
  match slot with
  | Some t when go t <> None -> go t
  | _ -> (
    match current_cpp_return_type_ir () with
    | Some rt -> go rt
    | None -> None )

(** Collapse the erased parts of a type to [std::any]: the type itself when it
    resolves to [std::any], and, structurally, a function type's arguments and
    result.  Lets an expected type argument be compared against a computed one
    on equal terms, the computed side already being erased. *)
let rec normalize_erased_types_ir : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | t when resolves_to_any_type_ir t -> Any
  | Function (ps, r) ->
    Function (List.map normalize_erased_types_ir ps, normalize_erased_types_ir r)
  | t -> t

(** How many of [id]'s leading template parameters no signature mentions,
    counted by {!Ml_type_util.explicit_tvar_prefix_ir} off its declared type: its
    leading phantoms.  Nothing deduces them, so a call writes them, and
    {!Callable_abi} records them as [Phantom] parameters of [id]'s plan.  The
    declaration emitter counts the same run and leaves those parameters
    undefaulted. *)
let leading_phantom_count id =
  match callee_ml_type id with
  | None -> 0
  | Some ml_ty ->
    let cty =
      cpp_ir_of_ml_type (empty_env ()) [] (type_simpl ml_ty)
    in
    let force_required = collect_ml_type_index_tvars ml_ty in
    explicit_tvar_prefix_ir ~force_required cty

(** The template name a written type [c] stands for at a higher-kinded
    variable: [c] itself as a constructor, unless applying it changes
    nothing -- [fun T => list nat], which extraction writes as its body
    [list nat] -- when it is the constant one, [crane::constant_tc<c>::c]. *)
let carrier_template env tvars c : Cpp_ir.Lowered.Type.t =
  let carrier = template_arg_of_ml_type_ir ~site:Through_tvar env tvars c in
  let constant = Mlutil.eq_ml_type (Mlutil.apply_ml_type c [Miniml.Tunknown]) c in
  Type_constructor
    (if constant then Member (External (Crane_rt.constant_tc, [carrier]), Id.of_string "c") else carrier)

(** The explicit type arguments a call needs when the callee is generic in a
    type {e constructor} and Rocq erased which one.

    A higher-kinded class parameter reaches the call as [Tdummy]: the carrier
    of [TFunctor (fun T => T * box T)] is a term Rocq computed away.  C++
    deduces the parameter from the value argument instead, by matching
    [T1<T2>] against the argument's type -- which works exactly when the
    carrier is a template name applied to one argument, and fails outright
    when it is not: [std::pair<Nat, Box<Nat>>] deduces [T1 = std::pair], a
    binary template where a unary one was declared.

    The carrier is recovered from the type the result is expected to have.
    The callee returns [Tapp (p, [Tvar v])] -- the carrier at position [p]
    applied to the variable at position [v] -- so abstracting the expected
    result over whatever [v] was instantiated to inverts that application.
    {!abstract_cpp_type_ir} writes the sentinel the printer mints an
    alias template for, and only position [p] is written: the rest deduce
    through the alias, which is transparent.

    Nothing is claimed where the abstraction does not fire.  If [v]'s
    instantiation does not occur in the result then the carrier is constant in
    its argument and the result says nothing about it, and if the result type
    is unknown there is nothing to read.

    Where extraction did name the carrier -- [list], or a constant [fun T =>
    list nat] -- it is written as it is: a parameter that applies it to an
    erased element, a rank-2 argument at [T1<std::any>], deduces nothing.  A
    constant one is a complete type that an application leaves unchanged
    ({!Mlutil.apply_ml_type}), and has no template to name: it is the type
    function {!Crane_rt.constant_tc} makes of it. *)
let hkt_carrier_type_args env tvars ?result id tys =
  Probe.changed "REPAIR_hkt_carrier_type_args" id ~before:None @@
  let ( let* ) = Option.bind in
  let* ml_ty = find_type_opt id in
  match Mlutil.Var_types.find_tvar tys 1 with
  | Some c
    when IntSet.mem 1 (Ml_type_util.higher_kinded_ml_tvars [ml_ty])
         && not (Mlutil.isTdummy (resolve_tmeta c))
         && not (ml_type_contains_erased c) ->
    Some [carrier_template env tvars c]
  | _ ->
  let* p, v =
    match resolve_tmeta (ml_return_type ml_ty) with
    (* Only a leading carrier is written: an explicit argument list is
       positional, so a carrier further in would need every argument before it
       spelled as well, and a class parameter is always quantified first. *)
    | Miniml.Tapp (1, [Miniml.Tvar (_, v)]) -> Some (1, v)
    | _ -> None
  in
  let* () =
    match Mlutil.Var_types.find_tvar tys p with
    | Some (Miniml.Tdummy _) -> Some ()
    | _ -> None
  in
  let* v_ml = Mlutil.Var_types.find_tvar tys v in
  let* result =
    match result with
    | None -> current_cpp_return_type_ir ()
    | r -> r
  in
  let over = template_arg_of_ml_type_ir ~site:Through_tvar env tvars v_ml in
  let* carrier = abstract_cpp_type_ir ~over result in
  (* A carrier that is one template applied to the argument is left to
     deduction, which reads it off the value argument and gets it right.  Only
     a carrier with no head to read -- a composite, or a partial application --
     has to be written, and it is written alone: everything after it deduces
     through the alias, which is transparent. *)
  let rec is_plain_head (t : Cpp_ir.Lowered.Type.t) =
    match t with
    (* A namespace or a const/reference wrapper is spelling, not structure. *)
    | In_namespace (_, t) | Const t | Reference (_, t) -> is_plain_head t
    | Entity_application (_, [arg], _) | Named (_, [arg]) | External (_, [arg]) | Apply (_, [arg]) ->
      arg = Carrier_parameter
    | _ -> false
  in
  if is_plain_head carrier then None else Some [(Type_constructor carrier : Cpp_ir.Lowered.Type.t)]

(** The explicit type arguments a call to a lifted helper has to carry.

    Lifting turns the body's type variables into template parameters of a new
    top-level function, and a parameter that occurs only in the {e return}
    type is deducible from nothing: the call must spell it or the overload is
    discarded.  [binder_ty] is the lifted thing's own ML type, whose codomain
    is matched against the enclosing function's C++ return type to say what
    each variable beyond [outer_tvars] stands for at this call.

    What the parameters already spell is left to deduction, because one
    explicit list stands for every reference while the instantiations need not
    agree -- a polymorphic local helper may be used at two types in one body.
    Explicit arguments are positional, so only a trailing deducible run can be
    dropped.

    Every lift path asks this, and the only difference between them is where
    the type and the parameters come from.  [all_tvar_names] is in index
    order, as type conversion reads it; the arguments follow the order of the
    [head], the type parameters the lifted template declares. *)
let lifted_call_type_args_ir
    ~(class_args : Cpp_ir.Lowered.Type.t list) ~env ~outer_tvars ~head ~all_tvar_names ~binder_ty ~param_ml_tys :
    Cpp_ir.Lowered.Type.t list =
  let in_head id = List.exists (Id.equal id) head in
  let outer_tvars = List.filter in_head outer_tvars in
  let all_tvar_names = List.filter in_head all_tvar_names in
  let in_head_order = List.filter (fun id -> List.exists (Id.equal id) all_tvar_names) head in
  class_args
  @
  let extra_tvar_names =
    List.filter
      (fun id -> not (List.exists (Id.equal id) outer_tvars))
      in_head_order
  in
  if extra_tvar_names = [] then
    List.map (fun id -> Cpp_ir.Build.named_variable id) outer_tvars
  else
    let tmpl_cod : Cpp_ir.Lowered.Type.t =
      match cpp_ir_of_ml_type env all_tvar_names binder_ty with
      | Function (_, cod) -> cod
      | t -> t
    in
    let tvar_map =
      match current_cpp_return_type_ir () with
      | Some conc_ret -> extract_tvar_map_ir tmpl_cod conc_ret
      | None -> []
    in
    let args =
      List.map (fun id -> Cpp_ir.Build.named_variable id) outer_tvars
      @ List.map
          (fun tvar_name ->
            match
              List.find_opt (fun (id, _) -> Id.equal id tvar_name) tvar_map
            with
            | Some (_, ty) -> ty
            | None -> (
              match current_cpp_return_type_ir () with
              | Some ret_ty -> ret_ty
              | None -> Cpp_ir.Build.named_variable tvar_name ) )
          extra_tvar_names
    in
    let deducible =
      List.concat_map
        (fun ml_ty ->
          get_tvars_ir (cpp_ir_of_ml_type env all_tvar_names ml_ty) )
        param_ml_tys
    in
    if List.length in_head_order <> List.length args then
      args
    else
      let rec strip = function
        | [] -> []
        | (id, ty) :: rest -> (
          match strip rest with
          | [] when List.exists (Id.equal id) deducible -> []
          | rest -> (id, ty) :: rest )
      in
      List.map snd (strip (List.combine in_head_order args))

(** The carrier of a higher-kinded class parameter, read off the {e dictionary}
    the call passes for that class.

    {!hkt_carrier_type_args} recovers a carrier from the type the result is
    expected to have, which needs the result to mention it.  An instance
    {e method} for a nested functor does not qualify: [TFunctor_list']'s result
    is [list (T1 B)], and by the time the call is built the expected type has
    already erased the element to [std::any], so there is nothing left to
    abstract over.

    What still knows the carrier is the dictionary argument.  A parameter of
    class type -- [TFunctor T1] -- is instantiated by the instance for exactly
    one type constructor, and that instance's method returns [T1] applied: the
    dictionary for [box] is a function whose codomain is [box B].  So the head
    of the dictionary's codomain {e is} the carrier.

    The dictionary reaches the call wrapped in the adapter lambda that erases
    its arguments, so the instance is found by descending to the head of the
    lambda's body.  It need not be an instance at all: where the enclosing
    function abstracts over the instance, the dictionary is a binder, and the
    carrier is written in the constraint that binder's own type spells.  Both
    sources end at an ML type headed by the carrier, and are consumed as one.

    Nothing is claimed when neither source yields a type, or when that type is
    not an application -- a carrier has to be applied to something to be one.

    Written unconditionally, unlike the result route: [T1] here occupies a
    non-deduced position ([std::type_identity_t<TFunctor<T1>>], and [T1<std::any>]
    against an already-erased argument), so even a carrier that is a plain
    template name has to be named rather than left to deduction. *)
let dict_carrier_type_args env tvars id args =
  Probe.changed "REPAIR_dict_carrier_type_args" id ~before:None @@
  let ( let* ) = Option.bind in
  let* cod =
    dict_carrier_ml_type ~lex:(current_lexenv ()) ~caller:!Table.current_decl_ref id args
  in
  (* Abstracted over the traversed type, as {!apply_hkt_tyctors_ir} does: the
     class applies its carrier to it and this idiom writes it first, so the two
     agree on one body and the printer mints one alias for both.

     The carrier need not apply to it {e directly}.  A composed carrier
     [fun t => option (Exp t)] reaches it through the constructors it composes,
     and the codomain's leading argument is then [Exp t] rather than [t];
     abstracting over that yields [option] alone -- the composition's outer
     head, which is the arity deduction would have guessed and precisely what
     a composition is not.  So the leading arguments are descended to the type
     that is not itself an application: that is what the whole composition is
     applied to, and where the carrier is a plain head the descent stops at
     once.

     Descended only where the composition is fully known.  An occurrence
     {!apply_carrier} declined to fill is left as the [Tapp] it was, and by
     then nothing tells it apart from one that was recovered; writing it out
     spells a carrier built partly from a class parameter that is in scope and
     is not the one meant.  There the leading argument is abstracted over as
     before, which yields the outer head alone -- still wrong, but wrong the
     way deduction is wrong, and absorbed wherever a converting constructor
     absorbs it.  A wrong spelling is worse than an unrecovered one.

     Only occurrences among the {e arguments} count.  The head may be a [Tapp]
     and be right: a carrier that {e is} a class parameter is written as that
     parameter, which the enclosing declaration has in scope. *)
  let rec unrecovered t =
    match resolve_tmeta t with
    | Miniml.Tapp _ -> true
    | Miniml.Tglob (_, targs, _) -> List.exists unrecovered targs
    | _ -> false
  in
  (* Which argument the composition is applied {e in}, which is a different
     question from how far to descend and only looks like the same one while
     every constructor in the chain takes a single argument.  The carrier is
     the method's codomain abstracted over the variable the method quantifies,
     so the argument to follow is the one that variable occurs in:
     [fun t => list (nat * Exp t)] reaches it through the {e second} component
     of the pair, and following the leading argument abstracts over [nat]
     instead -- a carrier of the right shape, varying in the wrong place, which
     nothing downstream can tell from the right one. *)
  let rec mentions_traversed t =
    match resolve_tmeta t with
    | Miniml.Tunknown | Miniml.Tvar _ -> true
    | Miniml.Tglob (_, targs, _) | Miniml.Tapp (_, targs) ->
      List.exists mentions_traversed targs
    | Miniml.Tarr (a, b) -> mentions_traversed a || mentions_traversed b
    | _ -> false
  in
  let rec traversed t =
    match resolve_tmeta t with
    | Miniml.Tglob (_, (t0 :: _ as targs), _)
    | Miniml.Tapp (_, (t0 :: _ as targs)) ->
      (* No argument mentioning it means there is nothing better to say than
         what the leading one says, which is what this did before. *)
      traversed (Option.default t0 (List.find_opt mentions_traversed targs))
    | t -> t
  in
  let* over =
    match resolve_tmeta cod with
    | Miniml.Tglob (_, (t0 :: _ as targs), _)
    | Miniml.Tapp (_, (t0 :: _ as targs)) ->
      let whole = if List.exists unrecovered targs then t0 else traversed cod in
      Some (template_arg_of_ml_type_ir ~site:Through_tvar env tvars whole)
    | _ -> None
  in
  let* carrier = abstract_cpp_type_ir ~over (template_arg_of_ml_type_ir ~site:Through_tvar env tvars cod) in
  Some [(Type_constructor carrier : Cpp_ir.Lowered.Type.t)]

(** Whether [e] denotes a value whose ML type is a function (at least one value
    arrow).  Used to decide, at a constructor argument that is stored into an
    erased ([std::any]) field, whether to route it through the [crane_erase_fn]
    runtime helper so the canonical [std::function<std::any(std::any...)>]
    representation is stored (matching the [any_cast] on the application side)
    rather than a raw closure.  An [MLrel] already erased to [std::any]
    ({!read_is_boxed}) is excluded: it is not callable, so wrapping it
    would miscompile.  [var i occ] says whether the read of the variable [i]
    at [occ] holds a box, and the variable's ML type: by default as lowering
    has them in scope. *)
let ml_expr_is_function_value ?(var = fun i occ -> (read_is_boxed i occ, get_env_type_opt i)) e =
  match strip_magic e with
  | MLrel (i, occ) ->
    let boxed, ty = var i occ in
    (not boxed) && ( match ty with Some t -> count_ml_value_arrows t >= 1 | None -> false )
  (* A partial application of a global whose codomain mentions a
     value-dependent erased type (e.g. [mk_action n : domty n -> bool]) is
     wrapped in [MLmagic] by the kernel's typing coercion even at the
     application node itself, not just around the whole expression — so
     [strip_magic] above (which only strips the outer expression) does not
     expose the [MLglob] underneath. Look through it here, locally, rather
     than in [infer_ml_body_type] itself (whose result also feeds unrelated
     callers like lambda return-type annotation), so this fix cannot change
     behavior anywhere but function-value detection. *)
  | MLapp (MLmagic (_, f, _), args) ->
    ( match infer_ml_body_type (MLapp (f, args)) with
    | Some t -> count_ml_value_arrows t >= 1
    | None -> false )
  | other ->
    ( match infer_ml_body_type other with
    | Some t -> count_ml_value_arrows t >= 1
    (* Inference is best-effort and gives up when a binder's type is itself a
       type-level computation ([sem (TArr a b)] for a [Fixpoint sem : ty ->
       Type]).  A syntactic lambda is a function value whatever its type, so
       fall back on the shape rather than on the failed inference. *)
    | None -> ( match other with MLlam _ -> true | _ -> false ) )

(** Whether [t] still has a hole extraction left open. *)
let rec has_open_meta t =
  match t with
  | Miniml.Tmeta {contents = None} | Miniml.Topen _ -> true
  | Miniml.Tmeta {contents = Some t} -> has_open_meta t
  | Miniml.Tarr (a, b) -> has_open_meta a || has_open_meta b
  | Miniml.Tglob (_, ts, _) -> List.exists has_open_meta ts
  | _ -> false

(** [slot_refined_lambda env ~expected_ml_ty args body] -- the binders [args]
    (innermost first) of a lambda over [body], and [body], as lowering
    generates them in a slot of ML type [expected_ml_ty]
    ({!Translation.gen_expr}'s [MLlam] case; [None] where the slot is a box
    or states none).

    A binder's recorded type is whatever extraction managed to infer for it,
    and a component it never inferred stays erased even where the rest of the
    type is spelled in full: [pair(list(pair(A, B)), Tdummy)] for a [x] the
    callee declares at [pair(list(pair(A, B)), list(B))].  The slot states the
    whole shape, so the binder is refined against it -- at the {e ML} type,
    before anything reads it.  The signature and the body are generated from
    this one type: correct it at the declaration and the body decomposes the
    pair at the type it really has, while correcting the spelling alone
    leaves the body unboxing at the erased view its own generation assumed
    (see {!Ml_type_util.refine_param_from_slot}, which for that reason may
    only refine as far as still-erased).  A signature's domains are in source
    order, so they index [args] the opposite way.

    A variable of the callee's the slot names and this scope does not --
    [TFunctor_block]'s [U], its instance emitted at [std::any] -- is erased
    where it sits, so the rest of the slot still describes the lambda.  Only
    where extraction left a binder open is it read at that erased view: an
    erased position is no information about a binder that has a type of its
    own ([state_get]'s [s : T1]).  A hole a binder's type is filled at is the
    hole the other binders' and the body's annotations mention -- the match
    destructuring the binder among them -- so they are filled too. *)
let slot_refined_lambda env ~expected_ml_ty args body =
  let rec erase_unscoped t =
    match resolve_tmeta t with
    | Miniml.Tvar _ as v when not (names_only_scoped_tvars_ir (cpp_of_ml_ir env v)) -> Miniml.Tunknown
    | Miniml.Tarr (a, b) -> Miniml.Tarr (erase_unscoped a, erase_unscoped b)
    | Miniml.Tglob (g, ts, l) -> Miniml.Tglob (g, List.map erase_unscoped ts, l)
    | t -> t
  in
  let fills = ref [] in
  let args =
    match expected_ml_ty with
    | Some fn_ty ->
      let rec domains ty =
        match resolve_tmeta ty with
        | Miniml.Tarr (d, cod) -> d :: domains cod
        | _ -> []
      in
      let doms = Array.of_list (domains fn_ty) in
      let n = List.length args in
      List.mapi
        (fun i (x, ty) ->
          if n - 1 - i >= Array.length doms then (x, ty)
          else
            let d = doms.(n - 1 - i) in
            let d = if has_open_meta ty then erase_unscoped d else d in
            (x, Ml_type_util.refine_erased ~fills ~writable:(fun t -> names_only_scoped_tvars_ir (cpp_of_ml_ir env t)) ty d) )
        args
    | None -> args
  in
  let args = List.map (fun (x, t) -> (x, Ml_type_util.fill_holes_type !fills t)) args in
  (args, Ml_type_util.fill_holes !fills body)

(* Whether [body] takes its single binder apart: matches on it, or applies to
   it a projection spelled as member access (an inline custom [%a0.first]). *)
let body_reads_members_of_binder body =
  let member_access g =
    Table.is_inline_custom g
    && ( match Table.find_custom_opt g with
       | Some txt ->
         String.length txt > 4 && String.sub txt 0 4 = "%a0."
       | None -> false )
  in
  let rec reads depth e =
    match e with
    | MLapp (MLglob {callee = g; _}, MLrel (k, _) :: _)
      when k = depth + 1 && member_access g ->
      true
    | MLlam (_, _, b) -> reads (depth + 1) b
    | MLletin (_, _, x, b, _) -> reads depth x || reads (depth + 1) b
    | MLcase (_, sc, pv, _) ->
      reads depth sc
      || Array.exists
           (fun (ids, _, _, br) -> reads (depth + List.length ids) br)
           pv
    | MLfix (_, ids, funs, _, _) ->
      Array.exists (reads (depth + Array.length ids)) funs
    | e ->
      let found = ref false in
      Mlutil.ast_iter (fun x -> if reads depth x then found := true) e;
      !found
  in
  (match body with
   | MLcase (_, MLrel (1, _), pv, _) -> is_custom_match pv
   | _ -> false)
  || reads 0 body

(* The type a match in [body] reads its single binder at, where that type has
   no parameters -- and so one spelling, which the body cannot be reading at
   some other, erased, view: [if b] states [bool] whatever the binder's own
   annotation lost. *)
let binder_matched_at body =
  let found = ref None in
  let rec walk depth e =
    match e with
    | MLcase ((Miniml.Tglob (_, [], _) as t), sc, _, _)
      when (match strip_magic sc with MLrel (j, _) -> j = depth + 1 | _ -> false)
           && !found = None ->
      found := Some t
    | MLlam (_, _, b) -> walk (depth + 1) b
    | MLletin (_, _, x, b, _) -> walk depth x; walk (depth + 1) b
    | MLcase (_, sc, pv, _) ->
      walk depth sc;
      Array.iter (fun (ids, _, _, br) -> walk (depth + List.length ids) br) pv
    | MLfix (_, ids, funs, _, _) -> Array.iter (walk (depth + Array.length ids)) funs
    | e -> Mlutil.ast_iter (walk depth) e
  in
  walk 0 body;
  !found

(** Whether binder [i] of a lambda's [binders] (innermost-first, over
    [body]) becomes a C++ parameter, the lambda written against a slot of C++
    type [expected_ty] ({!Translation.gen_expr}'s [MLlam]).  A binder typed
    [Tdummy] carries nothing, unless the body names it or the slot's
    declaration takes a value at its position: [Cat IFun]'s [cat] binds
    objects [a b c] that [obj := Type -> Type] erases, and [Cat] is a
    function of them all the same -- and only where the slot's own domain
    there is a box: an erased binder stands for an erased value, [Id_]'s
    object, never for the [Nat] state a [stateT] takes first.  A binder with
    no type ([Taxiom]) is one erasure took the type from -- [IFun]'s
    [forall T] -- and unused it is erased like a dummy.  The count of binders
    the term writes and the parameter list it is written with are both read
    off this, so they cannot disagree. *)
let lambda_binder_emitted_ir env ~(expected_ty : Cpp_ir.Lowered.Type.t option) ~body binders i ty =
  let slot_value_doms =
    let rec alias_ref (t : Cpp_ir.Lowered.Type.t) =
      match Cpp_ir.Types.strip_param_spelling t with
      | In_namespace (_, t) -> alias_ref t
      | Entity_application (GlobRef.ConstRef kn, _, _) -> Some kn
      | _ -> None
    in
    let rec value_doms t =
      match resolve_tmeta (expand_ml_fun_alias t) with
      | Miniml.Tarr (d, c) -> not (erased_by_extraction d) :: value_doms c
      | _ -> []
    in
    match Option.bind expected_ty alias_ref with
    | Some kn -> (
      match Table.lookup_typedef_unchecked kn with
      | Some body -> value_doms body
      | None -> [] )
    | None -> []
  in
  let slot_doms_cpp =
    match Option.map (unfold_cpp_typedef_ir env) expected_ty with
    | Some (Function (doms, _)) -> doms
    | _ -> []
  in
  let slot_keeps binders i =
    let d = List.length binders - 1 - i in
    match List.nth_opt slot_value_doms d with
    | Some true -> (
      match List.nth_opt slot_doms_cpp d with
      | Some t -> Cpp_ir.Types.prints_as_any t
      | None -> true )
    | _ -> false
  in
  slot_keeps binders i
  || (is_runtime_binder_type ty && ty <> Miniml.Taxiom)
  || Mlutil.ast_occurs (i + 1) body

(** The C++ type a lambda declares its parameter [(id, ty, owned)] at
    ({!Translation.gen_expr}'s [MLlam]), and the substitution its body is
    rewritten with, if any.  [slot_dom] is the domain the slot the lambda
    fills declares at this parameter's position, where it declares a
    signature; [unused], that the body never reads the parameter; [body], the
    lambda's body; [n_params], how many binders it has; [rank2_carrier], the
    template parameter a polymorphic function object writes its erased
    positions at; [reified], that itree terms are extracted reified.  Lowering
    passes what it is generating against, the representation plan what it
    reads off Core. *)
let lambda_param_cpp_type env ~ns ~tvars ~rank2_carrier ~reified ~n_params ~body ~unused ~slot_dom (id, ty, owned) =
  let at_carrier ty = match rank2_carrier with None -> ty | Some x -> Rank2.at_carrier x ty in
  let tvar_in_scope n = List.exists (Id.equal n) tvars in
  let slot_param_cpp_ty =
    (* Only a type this lambda could actually be written against.  The slot
       is read off the callee's declaration, so it may name that
       declaration's own template parameters, which are no more in scope here
       than the erasure was -- adopting one trades [std::any] for a free
       name. *)
    match slot_dom with
    | Some t
      when Id.Set.for_all tvar_in_scope (Cpp_ir.Types.variable_names t) ->
      Some t
    | _ -> None
  in
  let bare_cpp_ty =
    cpp_of_ml_ir env ty
  in
  let stored_cpp_ty =
    cpp_ir_of_ml_type env ~ns
      tvars ty
  in
  let body_subst =
    match (bare_cpp_ty, stored_cpp_ty) with
    | Entity_application (g1, [], _), Shared_pointer (Entity_application (g2, [], _))
      when globref_equal g1 g2 && Table.is_coinductive g2 ->
      Some (id, (Dereference (Local id) : Cpp_ir.Lowered.Expr.t))
    | _ -> None
  in
  let param_cpp_ty : Cpp_ir.Lowered.Type.t =
    match body_subst with
    | Some _ -> Reference (Lvalue, Const stored_cpp_ty)
    (* A binder the body never reads is a parameter only for its callers, and
       the slot's own spelling is the one they call it at:
       [Id_<std::any, ...>] takes its object as a box, whatever the binder's
       annotation recorded -- [MemE], the family the object stands for. *)
    | None when unused && Option.has_some slot_param_cpp_ty ->
      Option.get slot_param_cpp_ty
    (* The binder's annotation is a definition unfolded -- [FusedS] as
       [state * nat] -- and a class field in it names no instance in this
       scope, so it would fall back to the file-scope [std::any].  The slot
       writes the definition by name, which its own declaration resolved. *)
    | None
      when mentions_unresolved_promoted_ir bare_cpp_ty
           && Option.has_some slot_param_cpp_ty ->
      wrap_param_by_ownership_ir ~is_owned:owned
        (Option.get slot_param_cpp_ty)
    | None
      when rank2_carrier <> None
           && has_tany_in_type_ir bare_cpp_ty
           && not (Rank2.is_bare_box bare_cpp_ty) ->
      Reference (Lvalue, Const (at_carrier bare_cpp_ty))
    | None
      when Cpp_ir.Types.prints_as_any bare_cpp_ty
           && ( match slot_param_cpp_ty with
              | Some d -> not (Cpp_ir.Types.prints_as_any d)
              | None -> false ) ->
      (* The binder's own annotation says nothing -- a constructor eta-expanded
         into a lambda ([fmap inr m]) is handed a parameter extraction never
         gave a type -- but the slot it flows into does: the callee's
         instantiated domain.  Taking the type from there is what keeps the
         signature and the body in step, since the body was generated against
         the concrete type the constructor needs.  Written [std::any] instead,
         the parameter is a claim the body cannot keep, and the error lands
         inside the lambda at the use. *)
      wrap_param_by_ownership_ir ~is_owned:owned
        (Option.get slot_param_cpp_ty)
    | None
      when Ml_type_util.has_tany_written_ir bare_cpp_ty
           && n_params = 1
           && (body_reads_members_of_binder body || binder_matched_at body <> None) ->
      (* A pattern lambda: the body decomposes this parameter with a
         structured binding, which is ill-formed at [std::any].  Or it reads
         one of its members through a projection that is spelled as member
         access ([fst si] as [si.first]), which is ill-formed there just the
         same.  [crane_erase_fn] probes a generic callable with exactly that --
         and the binding is in the body, not the signature, so no [requires]
         can absorb the failure and the probe becomes a hard error.  Spelling
         the type keeps the probe well-formed: CTAD then deduces a signature,
         and the adapter unboxes at this very type, which is the one the
         producer boxed.

         Which type to spell is the slot's answer where it has one.  The
         binder's own is assembled from an ML type whose erased components
         were never inferred, so it erases a whole component the container
         keeps ([pair<Nat, std::any>] against a list of
         [pair<Nat, Exp0<std::any>>]); the slot spells the container's shape
         and leaves only the genuinely erased leaf to [std::any].

         It may refine the spelling only as far as still-erased, though.  The
         body was generated against the erased view and unboxes at it; a
         signature that erases nowhere is one the body's casts no longer agree
         with.  The exception is a match that reads the binder at a fully
         known type -- [if b] at [bool] -- since the body reads it at that
         type, uncast. *)
      let refined =
        match (binder_matched_at body, slot_dom) with
        | Some t, _ -> cpp_of_ml_ir env t
        | None, Some slot ->
          Ml_type_util.refine_param_from_slot_ir ~tvars ~slot
            bare_cpp_ty
        | None, None -> bare_cpp_ty
      in
      wrap_param_by_ownership_ir ~is_owned:owned refined
    | None
      when reified && ml_type_is_unit ty ->
      (* A reified tree's continuation is typed [unit -> itree ...] in ML, but
         [unit] is not one C++ type here: the value a reified tree carries is
         whatever its consumer chose, and the same Rocq type reaches the
         printer as [std::monostate] over a concrete tree and as [std::any]
         over one whose event type was erased.  The binder is under-determined
         rather than erased -- nothing in the term says which -- so it
         deduces.  Committing to [std::monostate] rejects every call through
         an erased tree.  The slot is still emitted; see the parameter filter
         in {!Translation.gen_expr}. *)
      Reference (Lvalue, Const Auto)
    | None when Ml_type_util.has_tany_written_ir bare_cpp_ty ->
      (* The type is spelled with erased positions (std::any).  Use
         [const auto&] so the C++ compiler deduces the concrete type at the
         call site -- explicit std::any in the param type would block valid
         calls and prevent field accesses inside the body from resolving to
         the concrete type.

         The erasure has to be one the spelling shows.  A type whose erased
         argument sits in a position its template never writes renders
         concretely, and a generic parameter there is a liability: a consumer
         that probes the callable with a [std::any] -- [crane_erase_fn] does --
         instantiates the body at [std::any] and fails inside it, where no
         [requires] can catch it. *)
      Reference (Lvalue, Const Auto)
    | None ->
      (* A function the slot takes at fewer domains than the binder's arrows
         flatten to -- [esc : A -> cont R B], with [cont R B] an alias for a
         function type -- is curried where the slot says ([Declared_at]). *)
      let declared_arity =
        match Option.map (unfold_cpp_typedef_ir env) slot_dom with
        | Some (Function (doms, _)) -> List.length doms
        | _ -> 0
      in
      wrap_param_by_ownership_ir ~is_owned:owned
        (if declared_arity > 0 then Cpp_ir.Types.spell_arrows (Declared_at declared_arity) bare_cpp_ty
         else bare_cpp_ty)
  in
  (param_cpp_ty, body_subst)

(** The C++ type a lambda parameter of ML type [ml_ty] declared [declared]
    ({!lambda_param_cpp_type}) is read at in its body.  A binder erasure would
    have removed, kept because the slot takes it ({!binder_emitted}), holds
    whatever box the caller passes.  So does one the slot declares erased
    ([slot_dom]), even though it is declared [const auto &] so the deduction
    can also land on a concrete type: assigned [std::any], uses inside the
    body recover their own type from it, where the [Tauto] the declaration
    strips to would say, wrongly, that the value is already what the body
    wants. *)
let lambda_param_assigned ~slot_dom ml_ty (declared : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  if erased_by_extraction ml_ty then Any
  else
    match (declared, slot_dom) with
    | Reference (Lvalue, Const Auto), Some d when Cpp_ir.Types.prints_as_any d -> Any
    | _ -> declared

(** Whether argument [i] of constructor [r] is forwarded unboxed by the
    constructor's custom template ([%a<i>] and nothing else): a pure
    type-level erasure marker such as [sum1], with no field storage to box
    into. *)
let ctor_arg_is_passthrough r i =
  match r with
  | GlobRef.ConstructRef ((kn, mi), cidx) ->
    ( try
        let tmpl = List.nth (Table.find_custom_ctor_templates (kn, mi)) (cidx - 1) in
        String.trim tmpl = Printf.sprintf "%%a%d" i
      with _ -> false )
  | _ -> false

(** The template arguments a custom constructor annotated [ty] is drafted
    at, before its destination refines them ({!Translation.gen_expr_custom_cons}):
    the inductive's parameters, converted, where every one erases the
    promoted types of [promoted_active]'s arity or, failing that, [return]'s
    arguments when it is the same inductive; an unresolved one written down as
    a box ({!Ml_type_util.materialise_opaque}). *)
let ctor_draft_temps_ir env ~promoted_active ~(return : Cpp_ir.Lowered.Type.t option) (ty : ml_type) =
  let temps =
    match ty with
    | Miniml.Tglob (cn, raw_tys, _) ->
      let tys =
        match cn with
        | GlobRef.IndRef (kn, _) -> (
          match Table.get_ind_num_param_vars_opt kn with
          | Some nv -> safe_firstn nv raw_tys
          | None -> raw_tys )
        | _ -> raw_tys
      in
      let temps = template_params_of_ml_ir ~site:Through_tvar env tys in
      if List.for_all Cpp_ir.Types.prints_as_any temps && promoted_active then
        match promoted_tys_of_arity_ir (List.length tys) with
        | Some promoted_tys -> promoted_tys
        | None -> temps
      else if List.for_all Cpp_ir.Types.prints_as_any temps then
        match return with
        | Some (Entity_application (rn, rargs, _))
          when GlobRef.CanOrd.equal rn cn
               && List.length rargs = List.length temps
               && not (List.exists Cpp_ir.Types.prints_as_any rargs) ->
          rargs
        | _ -> temps
      else temps
    | _ -> []
  in
  List.map materialise_opaque_ir temps

(** Whether argument [e], at index [i] of constructor [r], is a function
    stored via [crane_erase_fn] into an erased field: the field is at a type
    parameter of the inductive ([field_tys], dummies dropped) whose template
    argument ([temps]) prints as [std::any], and the constructor's template
    does not forward the argument as it is. *)
let stores_erased_fn_ir ?var env r ~field_tys ~(temps : Cpp_ir.Lowered.Type.t list) i e =
  match List.nth_opt field_tys i with
  | Some (Miniml.Tvar (_, j)) -> (
    match List.nth_opt temps (j - 1) with
    | _ when ctor_arg_is_passthrough r i -> false
    | Some t when Cpp_ir.Types.prints_as_any (unfold_cpp_typedef_ir env t) -> ml_expr_is_function_value ?var e
    | _ -> false )
  | _ -> false

(** [e], a constructor argument {!stores_erased_fn_ir} says is stored via
    [crane_erase_fn], as lowering generates it: a lambda is only ever invoked
    with its whole argument boxed as one [std::any] holding the fully erased
    representation ([pair<any,any>] for a pair domain), so a custom match on
    its own parameter reads the scrutinee as erased
    ({!mark_own_param_for_pair_erasure}); a parameter whose type converts with
    no erased position -- a literal index picking a concrete branch of a type
    family -- is erased to [std::any] so that the cast on it compiles. *)
let erased_fn_lambda env e =
  match strip_magic e with
  | MLlam (id, ty, body) ->
    if Ml_type_util.has_tany_in_type_ir (cpp_of_ml_ir env ty) then
      MLlam (id, ty, mark_own_param_for_pair_erasure 1 body)
    else MLlam (id, Miniml.Tunknown, mark_own_param_for_pair_erasure 1 body)
  | _ -> e

(** [is_boxed_source t] -- whether a value whose C++ type is [t] is
    physically inside a [std::any], and so may be read back out with an
    [any_cast].

    {!Ml_type_util.is_boxed_type_ir} answers this structurally, which misses a
    named alias for the box: a [Type]-valued definition is emitted as
    [using sel = std::any], and only following the alias chain reveals that a
    parameter of type [sel] is a box.  An opaque type is deliberately
    excluded -- it prints as [std::any] without promising one, so nothing may
    be cast out of it. *)
let is_boxed_source (t : Cpp_ir.Lowered.Type.t) =
  is_boxed_type_ir t
  ||
  match t with
  | Obligation Opaque_type -> false
  | Entity_application _ -> resolves_to_any_type_ir t
  | _ -> false

(** [classify_erasure ty] -- the erasure status of one side of a value
    boundary, as the single question worth asking about it.

    Three answers are easy to confuse, and the difference decides whether a
    value may be boxed, [any_cast] out of, or left alone:

    - [`Unknown] -- the type was not tracked. Boxing into such a slot is
      allowed; casting {e out} of it never is, since nothing says a box is
      there.
    - [`Boxed] -- the value really is inside a [std::any], so an [any_cast]
      recovers it.  Follows alias chains: a [Type]-valued definition emitted
      as [using sel = std::any] is a box under a name.
    - [`Opaque] -- spelled [std::any] but promising nothing about the
      representation (an opaque type).  Distinct from [`Unknown]: there
      the type is untracked, here it is untrackable.  Nothing may be boxed or
      cast on the strength of it.
    - [`Concrete t] -- an ordinary type.

    Prefer this to assembling an answer out of {!Ml_type_util.prints_as_any},
    {!Ml_type_util.is_boxed_type} and {!resolves_to_any_type} at each site:
    those sit at different layers (see [ml_type_util.mli]) and a site that
    picks the wrong one silently gets [false]. *)
let classify_erasure : Cpp_ir.Lowered.Type.t option -> _ = function
  | None -> `Unknown
  | Some f when is_boxed_source f -> `Boxed
  | Some f when Cpp_ir.Types.prints_as_any f -> `Opaque
  | Some f -> `Concrete f

(** [spells_as_any_ir t] -- whether [t] is written [std::any] in the
    generated code, following the alias chains that
    {!Cpp_ir.Types.prints_as_any}, being structural, cannot see through. *)
let spells_as_any_ir t = Cpp_ir.Types.prints_as_any t || resolves_to_any_type_ir t

(** [coerce ?term ?from ~into expr] adapts [expr] across a representation
    boundary: it is the single place that decides between boxing, [any_cast],
    [crane_erase_fn] and doing nothing.

    It first classifies the source side as boxed, opaque, concrete or unknown,
    and then reads the answer off that.  The classification rests on
    {!Ml_type_util.is_boxed_type_ir}, not on {!Cpp_ir.Types.prints_as_any}:
    an opaque type also prints as [std::any], but it is an admission that
    the representation is unknown, and nothing may be boxed or cast on the
    strength of it.  A boundary with an opaque type on either side is therefore
    left alone, for the representation-tolerant helpers in [crane_fn.h] to
    sort out at instantiation time.  The pointer dimension (bare value versus
    [shared_ptr]) is delegated to {!gen_type_conversion_expr}, which already
    handles it.

    Omit [from] where the value's C++ type is not tracked -- a freshly
    generated constructor argument, say.  The value is then taken to be
    concrete but unnamed, which licenses boxing it (boxing any value is
    well-formed) but never an [any_cast] out of it, which would be a claim
    about a representation we cannot see.

    [term] is the ML expression [expr] was generated from.  It is consulted
    only for the one question a missing [from] leaves open: whether the value
    is a function, and so has to be adapted by [crane_erase_fn] before it is
    boxed. *)
let rec coerce ?term ?(from : Cpp_ir.Lowered.Type.t option) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let source = classify_erasure from in
  let same_type = match from with Some f -> cpp_ty_eq_ir f into | None -> false in
  if same_type || into = Void then expr
  else
    match source with
    (* Casting a box to a name that is itself the box is not a recovery but
       an [any_cast<std::any>], which only succeeds on a doubly-boxed value
       and otherwise throws. *)
    | `Boxed when spells_as_any_ir into -> expr
    (* A closure built here is not a box, whatever its erased type says: what
       is boxed is what it returns -- [@id lit] eta-expanded, with [id : ID]
       erased to [std::any id(std::any)], read at [Endo<lit>].  Its returns
       are recovered at the codomain instead. *)
    | `Boxed when (match expr with Lambda _ -> true | _ -> false) -> (
      match (expr, unfold_cpp_typedef_ir (empty_env ()) into) with
      | Lambda l, Function (_, cod) ->
        let rec at_returns : Cpp_ir.Lowered.Stmt.t -> Cpp_ir.Lowered.Stmt.t = function
          | Return (Some e) -> Return (Some (coerce ~from:Any ~into:cod e))
          | st -> Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:Fun.id ~stmt:at_returns ~type_:Fun.id ()) st
        in
        Lambda
          { l with
            return_type =
              (match l.return_type with Some t when Cpp_ir.Types.prints_as_any t -> Some cod | r -> r);
            body = List.map at_returns l.body }
      | _ -> expr )
    (* Already recovered; a second cast would be reading the same box twice. *)
    | `Boxed -> (
      match expr with
      | Any_cast _ -> expr
      | _ -> (
        (* A list went into the box with its elements boxed, so that is the
           shape the cast has to name however concrete the context's element
           type is; the converting constructor then recovers each element. *)
        match Cpp_erasure.erased_list_shape_ir into with
        (* A custom list has no converting constructor to unbox its elements
           with, so it stays at the flat shape until a consumer converts it. *)
        | Some (g, shape) when Table.is_custom g -> Cpp_erasure.unbox_ir shape expr
        | Some (_, shape) -> Cpp_erasure.converting_ctor_ir into [Cpp_erasure.unbox_ir shape expr]
        | None -> Cpp_erasure.unbox_ir into expr ) )
    (* Nothing may be boxed or cast on the strength of an admission that the
       representation is unknown. *)
    | `Opaque -> expr
    | (`Unknown | `Concrete _) as concrete_source -> (
      let is_function_value =
        match concrete_source with
        | `Concrete (Function _) -> true
        | `Concrete _ -> false
        | `Unknown -> ( match term with Some t -> ml_expr_is_function_value t | None -> false )
      in
      if is_boxed_type_ir into then
        (* Boxing is not idempotent: [std::any] holding a [std::any] is a box
           no consumer opens twice. *)
        match expr with
        | Box (Any, _) | Any_cast (Any, _) -> expr
        | _ ->
          (* A closure does not survive as itself: the consumer recovers it with
             [any_cast<std::function<std::any(std::any...)>>], so it is adapted
             to that canonical shape first.  It is then boxed like any other
             value -- a custom constructor template such as [std::make_pair]
             deduces its field type from the argument, and an unboxed
             [std::function] would store [pair<any, function<any(any)>>] where
             the consumer expects [pair<any,any>]. *)
          let adapted =
            if is_function_value then wrap_crane_erase_fn Boxed_whole (erased_fn_instantiation expr) else expr
          in
          Cpp_erasure.converting_ctor_ir Any [adapted]
      else
        match into with
        (* A slot that erased its domain -- a record field whose Rocq type is
           [dty -> nat] at a value-dependent [dty], so
           [std::function<uint64_t(std::any)>] -- does not accept a closure
           written at the concrete domain, nor a generic lambda (which has no
           signature to convert from).  It takes one through the same
           [crane_erase_fn] adapter an erased parameter uses, whether or not the
           result erased along with the arguments. *)
        | Function (_, cod) when is_function_value && erased_domain_fun_ty_ir into ->
          wrap_crane_erase_fn (At_signature cod) expr
        (* The mirror image: a callable whose result erased -- a constant
           whose Rocq type hides its quantifier behind a type alias, or whose
           result a type index alone pins down -- reaching a slot that names
           that result concretely.  It is called through a lambda that gives
           each argument the shape the callable declares and recovers what it
           returns. *)
        | Function (dom, cod)
          when (not (Cpp_ir.Types.prints_as_any cod))
               &&
               match concrete_source with
               | `Concrete (Function (_, scod)) -> Cpp_ir.Types.prints_as_any scod
               | _ -> false ->
          let sdom, scod =
            match concrete_source with
            | `Concrete (Function (d, c)) -> (d, c)
            | _ -> ([], Any)
          in
          let params = adapter_params ~prefix:"_ue" dom in
          let args =
            List.mapi
              (fun i ((ty, _) as p) ->
                let into = Option.default Cpp_ir.Type.Any (List.nth_opt sdom i) in
                coerce ~from:ty ~into (adapter_arg p) )
              params
          in
          let call = coerce ~from:scod ~into:cod (Cpp_ir.Build.call expr args) in
          Cpp_ir.Build.lambda params None [Return (Some call)] ~capture:Stored
        | _ -> (
          match concrete_source with
          | `Concrete f when not (Cpp_ir.Types.prints_as_any into) ->
            gen_type_conversion_expr ~src_ty:f ~dst_ty:into expr
          | _ -> expr ) )

(** [regroup_crossing ~from ~into expr]: [expr], whose C++ type is [from],
    read at [into] where the two differ only in how their arrows are grouped
    ({!Minicpp.arrow_site}) -- a value spelled where it was declared reaching
    a slot a type argument spells curried, or back.  [crane_convert] regroups
    every function the value holds ([crane_cast_to] for [crane::fn] of
    another arity).  A function value itself is not this: it reaches a slot
    through the adapter {!Translation_calls.curry_value_to_expected} writes,
    whose type is the slot's. *)
let regroup_crossing ~(from : Cpp_ir.Lowered.Type.t) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let from = strip_cpp_ref_const_ir from and into = strip_cpp_ref_const_ir into in
  match (from, into) with
  | Function _, _ | _, Function _ -> expr
  | _ when from = into || not (Cpp_ir.Types.same_arrows from into) -> expr
  | _ when Cpp_ir.Types.prints_as_any from || Cpp_ir.Types.prints_as_any into -> expr
  | _ -> Convert (into, expr)

(** The C++ type the value [e] has where that is known without generating
    it: a variable's binder type as planned, a global value's declared type.
    [None] for anything else.  [agree] says when the planned and the
    recorded binder type give the caller one answer
    ({!planned_binder_type_or_derive}). *)
let value_cpp_type ~agree env e =
  match strip_magic e with
  | MLrel (j, occ) -> planned_binder_type_or_derive ~use:"value's type" ~agree env j occ
  | MLglob ({callee = r; _} as use) when Mlutil.Var_types.is_empty (Mlutil.written_type_args use) ->
    Option.map (cpp_of_ml_ir env) (callee_ml_type r)
  | _ -> None

(** Whether a coercion is one the Rocq indices rule out, rather than one C++
    can perform.

    Extraction records [Mcoerce (unit, nat)] for the [vnil] branch of a match
    on [vec (S n)] whose [return] clause computes [unit] there: a branch whose
    type differs from the type the match was instantiated at is one the
    scrutinee's index makes impossible.  [unit] is where this shows up
    unambiguously -- it carries no information, so no value of it can be
    converted to anything else, and a position holding one at another type can
    only be a position that is never reached.  What it returns is immaterial,
    and the only thing writable at an impossible type is an abort.

    The mirror is {!Gen_functions.dead_unit_returns_to_abort}, which catches the
    same branch where extraction recorded no coercion at all and a bare [tt]
    reaches a [return]; both throw {!Minicpp.dead_branch_message}. *)
let absurd_coercion_ir from (into : Cpp_ir.Lowered.Type.t) =
  Ml_type_util.ml_type_is_unit from
  && (not (is_cpp_unit_type_ir into))
  && into <> Void
  && not (resolves_to_any_type_ir into)

(** A list computed at a concrete element type (a call's result, a variable)
    going into a [Family_box] slot ([den t]): the family's generic consumers
    read it with every level boxed in turn -- its elements, and their
    components and elements -- so it is boxed at that shape
    ([crane_deep_box]), whatever container the [list] mapping makes it.  A
    literal needs no conversion, being built at the erased shape already (its
    slot is [Boxed]). *)
let deep_box_list e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match strip_magic e with
  | MLcons _ -> expr
  | e -> (
    match
      Option.bind (infer_ml_body_type e) (fun t -> Cpp_erasure.erased_list_shape_ir (cpp_of_ml_ir (empty_env ()) t))
    with
    | Some _ -> Cpp_ir.Build.call (Runtime Crane_rt.Deep_box) [expr]
    | None -> expr )

(** Adapt a value being stored into a boxed slot of kind [kind] to the shape
    its consumers read back out of the box.  A function value is read with
    [any_cast<std::function<std::any(std::any)>>], which is what the
    [crane_erase_fn] runtime helper builds, deducing the callable's signature
    with [std::function] CTAD; a list in a [Family_box], by
    {!deep_box_list}.  A [Var_box] -- an existential's payload -- is read at
    whatever type its consumer knows, and keeps any other value as it is, as
    does a callable already adapted. *)
let box_for_any_slot kind e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match expr with
  | Erase_callable _ -> expr
  | _ when ml_expr_is_function_value e -> wrap_crane_erase_fn Boxed_whole expr
  | _ -> ( match kind with Family_box -> deep_box_list e expr | Var_box -> expr )

(** True when environment variable at de Bruijn index [i] has an erased C++
    type (i.e. [std::any] or a dummy type, arising from dependent-parameter
    collapse).  Returns [false] if [i] is out of range.

    This deliberately converts the binder's ML type under [tvars] rather than
    reading {!binder_cpp_type}, and it is not a re-derivation of the binding
    site's answer: the two say different things, and callers pair them
    precisely to tell those things apart.  A binder the assignment types
    concretely, whose ML type is an out-of-scope variable, is a value held in
    a box under a concrete static type -- exactly the one that has to be
    unboxed.  Reading the assignment here would collapse the contrast and
    drop the [any_cast] (measured: [existential_erased_apply_bad_cpp] and
    [list_cons_erasure_bleed] stop casting). *)
let is_env_var_erased env tvars i =
  match get_env_type_opt i with
  | Some ml_ty ->
    Cpp_ir.Types.prints_as_any (cpp_ir_of_ml_type env tvars ml_ty)
  | None -> false

(** Check whether an ML expression's C++ type is erased ([std::any]).
    Used by the [MLmagic] handler to decide whether [any_cast] is needed. *)
let rec ml_expr_is_erased env (t : ml_ast) : bool =
  let tvars = get_current_type_vars () in
  match t with
  | MLrel (i, _) -> is_env_var_erased env tvars i
  | MLapp (f, args) ->
    let n_value_args =
      List.length (List.filter (fun a ->
        match a with MLdummy _ -> false | _ -> true) args)
    in
    let ml_ty_opt = match f with
      | MLglob {callee = r; _} -> find_type_opt r
      | MLrel (i, _) -> get_env_type_opt i
      | _ -> None
    in
    ( match ml_ty_opt with
      | Some ml_ty -> ml_codomain_erases_to_any n_value_args ml_ty
      | None -> false )
  | MLglob {callee = r; _} ->
    ( match callee_ml_type r with
      | Some ml_ty -> Cpp_ir.Types.prints_as_any (cpp_of_ml_ir env ml_ty)
      | None -> false )
  | MLmagic (_, inner, _) -> ml_expr_is_erased env inner
  | MLcase (case_ty, _, _, _) ->
    ( match case_ty with
      | Miniml.Tvar (_, _) | Miniml.Tunknown -> true
      | _ -> false )
  | _ -> false

(** The C++ type a read of record field [fld] has, out of a value of ML type
    [typ]: the field's declared type at the record's instantiation, stored as
    the record stores it.  [None] where [typ] is not a record naming [fld]. *)
let record_field_cpp_ty_ir env typ fld : Cpp_ir.Lowered.Type.t option =
  match resolve_tmeta typ with
  | Miniml.Tglob (r, args, _) -> (
    let declared =
      List.find_map
        (fun (f, ty) ->
          match f with
          | Some f when GlobRef.CanOrd.equal f fld -> Some ty
          | _ -> None )
        (Table.record_field_bindings_of_type typ)
    in
    match declared with
    | Some ml_ty -> (
      try
        Some
          (cpp_ir_of_ml_type env ~ns:(Ref.User.Set.singleton r)
             (get_current_type_vars ())
             (Mlutil.type_subst_list args ml_ty))
      with e when CErrors.noncritical e -> None )
    | None -> None )
  | _ -> None

(** [recover_boxed_component into e] opens the box when [e] is evidently a
    component read out of a pair that was recovered from one.  The context's
    type [into] is what the value is declared to be; the emitted expression is
    the evidence that it is physically a [std::any]. *)
let recover_boxed_component into (e : Cpp_ir.Lowered.Expr.t) =
  if yields_boxed_component e then coerce ~from:Any ~into e else e

(** Whether an [MLmagic] node says its subterm is physically inside a
    [std::any] here, and so has to be opened before it can be used.

    A [Mbarrier] carries no type gap at all.  An [Mcoerce] is a box only when
    one of its two types erases at this instantiation: a coercion between two
    types that are both written down concretely -- a typeclass carrier
    resolved by the instance being generated, say -- is a static mismatch the
    C++ types already agree on, and casting on account of it would read a box
    that was never built. *)
let magic_is_boxed env = function
  | Mboxed -> true
  | Mbarrier -> false
  | Mcoerce (from, into) ->
    let erases ty = ml_erases_to_box env ty in
    erases from || erases into

(** [recover_erased_scrutinee env ~is_magic typ expr] casts a scrutinee that is
    carried at runtime as [std::any] -- an existential witness, say -- back to
    [typ], the inductive recovered from the branch patterns.  Neither the
    [switch] of an enum match nor the [v()] of a variant match is applicable to
    a [std::any].  When [typ] itself erases there is nothing to recover to and
    the scrutinee is returned unchanged. *)
let recover_erased_scrutinee env ~is_magic typ (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  if not is_magic then expr
  else
    let cpp_ty = cpp_of_ml_ir env typ in
    if Cpp_ir.Types.prints_as_any cpp_ty then expr else Cpp_erasure.unbox_ir cpp_ty expr

(** Build the qualified constructor struct type for a pattern match branch.

    For [list<int>::Cons], this produces
    [Member (In_namespace (r, Entity_application (r, temps, \[\])), ctor_name)].
    Local inductives omit the namespace wrapper to avoid double qualification. *)
let ctor_type_of_match env (typ : ml_type) (cname : GlobRef.t) : Cpp_ir.Lowered.Type.t =
  let ctor_name = ctor_struct_id_of_ref cname in
  match typ with
  | Tglob (r, tys, _) ->
    let tys = List.map type_simpl tys in
    let tys =
      match r with
      | GlobRef.IndRef (kn, _) ->
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars ->
          (* A class template has to be spelled with all of its arguments.
             The scrutinee's type can be short of them -- the body of an
             instance method is extracted against the class's erased carrier,
             so it carries none at all -- and what is missing is precisely
             what erased: [std::any], which is what the method's own
             signature spells for the same type. *)
          let tys = safe_firstn num_param_vars tys in
          tys
          @ List.init
              (max 0 (num_param_vars - List.length tys))
              (fun _ -> Miniml.Tunknown)
        | None -> tys )
      | _ -> tys
    in
    (* The constructor struct is nested in the instantiation, so it has to be
       qualified by the same one the declaration spells: an inductive's
       argument at the flat arity a stored value has (see
       {!template_arg_of_ml_type_ir}). *)
    let temps =
      ind_promoted_type_args_ir r
      @ apply_hkt_tyctors_ir r (template_params_of_ml_ir ~site:Declared env tys)
    in
    Member (inductive_type_ir r temps [], ctor_name)
  | _ -> Named (ctor_name, [])

(** [unbox_value into e] recovers [e], a value known to come out of a box, at
    [into]: {!coerce} from [std::any]. *)
let unbox_value into (e : Cpp_ir.Lowered.Expr.t) = coerce ~from:Any ~into e

(** [recover_boxed_result_ir ~boxed ~expected expr] casts the result of a call
    back into the type the position expects -- see {!position_cpp_ty_ir} -- when
    [boxed]
    says the callee hands back a [std::any] whatever its ML type claims,
    because its codomain erases or because it was itself recovered from a box
    and so goes through the canonical [std::function<std::any(std::any...)>]
    adapter.

    [boxed] is a statement about the callee, not a guess, so the recovery is
    unconditional: unlike {!unbox_into_ir} it casts at a template parameter too,
    which inside a template is the one name the result has. *)
let recover_boxed_result_ir ~boxed ~expected expr =
  match position_cpp_ty_ir expected with
  | Some into when boxed -> coerce ~from:Any ~into expr
  | _ -> expr

(** [unbox_into_ir into e] recovers [e] from its box at [into], where the
    position stated a type to recover it at, and leaves it boxed otherwise. *)
let unbox_into_ir into e =
  match into with
  | Some into when states_unboxed_target_ir into -> coerce ~from:Any ~into e
  | _ -> e

(** What a custom match over [t], annotated [typ], with branches [pv], knows
    about whether its scrutinee is boxed, as {!Translation.gen_custom_cpp_case}
    decides it: [var_boxed i occ] says whether the variable read at [occ],
    of the binder at de Bruijn index [i], holds a box, [var_type] gives a
    binder's ML type.  Reads no binder itself. *)
type custom_scrutinee = {
  cs_mlmagic : bool;  (** a coercion that boxes *)
  cs_cpp_erased : bool;  (** a variable whose binder holds a box *)
  cs_magic : bool;  (** either, or a variable whose ML type erases to a box *)
  cs_callee_ret_erased : bool;  (** a call whose declared codomain is a box *)
  cs_typ : Cpp_ir.Lowered.Type.t;  (** the annotation, converted *)
  cs_concrete : Cpp_ir.Lowered.Type.t;  (** the inductive the patterns recover, where [cs_typ] erases *)
  cs_pair : GlobRef.t option;  (** that inductive, when it is a pair *)
  cs_pair_any_cast : bool;  (** the pair is read back as [pair<any, any>], every field a box *)
}

(** A spine read whole, through the coercions around its head. *)
let rec flatten_app = function
  | MLapp (f, args) ->
    ( match flatten_app f with
    | MLapp (f', inner_args) -> flatten_app (MLapp (f', inner_args @ args))
    | f' -> MLapp (f', args) )
  | MLmagic (_, e, _) -> flatten_app e
  | other -> other

let custom_match_scrutinee env (typ : ml_type) t pv ~var_boxed ~var_type =
  (* [scrut_is_magic]: true when the scrutinee is erased at runtime (stored as
     [std::any]) even though the ML AST may carry a concrete type annotation.
     Covers both explicit [Obj.magic] wrappers and variables retyped to [Tany]
     by an outer [fix_a_fired] pair match (detected via its binder). *)
  let scrut_is_mlmagic = match t with MLmagic (m, _, _) -> magic_is_boxed env m | _ -> false in
  let scrut_is_cpp_erased = match t with
    | MLrel (i, occ) -> var_boxed i occ
    | _ -> false
  in
  let scrut_is_magic = match t with
    | MLmagic (m, _, _) -> magic_is_boxed env m
    | MLrel (i, occ) ->
      var_boxed i occ
      || (match var_type i with
          (* An ML type that erases on its own may still have been written
             down concretely here -- a typeclass carrier resolved by the
             instance being generated, say -- in which case the binder holds
             the value itself and there is no box to open. *)
          | Some ty ->
            is_erased_ml_type ty
            && ml_erases_to_box env ty
          | None -> false)
    | _ -> false
  in
  (* [scrut_callee_ret_erased]: the scrutinee is a call to a global function
     ([MLapp (MLglob {callee = r; _}, args)], possibly [MLmagic]-wrapped) whose
     DECLARED (un-instantiated) codomain resolves to [std::any] — e.g.
     [rev_tuple : forall xs, syms_semty xs -> syms_semty (rev xs)], a single
     C++ function generic over [xs], so its actual return type is the
     value-dependent-erased [syms_semty] regardless of how a specific
     call-site's Rocq type-checker happened to reduce the annotated result
     type (e.g. to a concrete [prod] when [xs] is a literal list). Using the
     call-site-reduced [typ] alone under-detects this: it looks concrete even
     though the callee only ever returns [std::any] at the C++ level. *)
  let scrut_callee_ret_erased =
    match flatten_app t with
    | MLapp (MLglob ({callee = r; _} as use), args) ->
      ( match callee_ml_type r with
      | Some fty ->
        let fty = Mlutil.instantiate_written ~reader:"scrut_callee_ret_erased" use fty in
        ( match strip_tarr_n (count_real_ml_args args) fty with
        | Some rty ->
          (* Both spellings of "is a [std::any] at run time" are needed here:
             [resolves_to_any_type] follows a named alias for the box, and
             [prints_as_any] catches the codomain a callee left as an erased
             type argument, which converts to a dummy glob rather than to
             [Tany]. *)
          let rty_cpp = cpp_of_ml_ir env rty in
          spells_as_any_ir rty_cpp
        | None -> false )
      | None -> false )
    | _ -> false
  in
  let typ = cpp_of_ml_ir env typ in
  (* [concrete_match_type]: when [typ] is erased ([std::any]), recover the
     actual inductive type from the first branch's pattern constructor and
     its field types.  Used for non-pair matches (e.g. option, variant) where
     we need to emit [any_cast<ConcreteType>(scrut)]. *)
  let concrete_match_type : Cpp_ir.Lowered.Type.t =
    if spells_as_any_ir typ || scrut_callee_ret_erased then
      try
        let _, _, pat0, _ = pv.(0) in
        let ind_ref = match pat0 with
          | Pusual (GlobRef.ConstructRef (ip, _))
          | Pcons (GlobRef.ConstructRef (ip, _), _) -> GlobRef.IndRef ip
          | _ -> raise Not_found
        in
        let ids0, _, _, _ = pv.(0) in
        let tyargs = List.rev_map (fun (_, ty) ->
          erase_unresolved_tvars_ir (cpp_of_ml_ir env ty)
        ) ids0 in
        Entity_application (ind_ref, tyargs, [])
      with _ -> typ
    else typ
  in
  let pair_g_opt = match concrete_match_type with
    | Entity_application (g, _, _) when is_prod_global g -> Some g
    | _ -> None
  in
  let scrut_is_trivial_ml = match t with
    | MLrel _ | MLmagic (_, MLrel _, _) -> true
    | _ -> false
  in
  let needs_pair_any_cast =
    pair_g_opt <> None &&
    ( scrut_is_cpp_erased || scrut_is_mlmagic || scrut_callee_ret_erased
      || (scrut_is_magic && Cpp_ir.Types.prints_as_any typ)
      (* Read off the type only where nothing says otherwise: a variable
         is boxed exactly when its binder is ([scrut_is_magic]), and one
         declared [pair<std::any, exp<std::any>>] holds that pair. *)
      || (not scrut_is_trivial_ml)
         && (is_all_erased typ || resolves_to_any_type_ir typ) &&
         ( Ml_type_util.has_tany_in_type_ir concrete_match_type
           || (match concrete_match_type with
               | Entity_application (_, args, _) -> List.exists resolves_to_any_type_ir args
               | _ -> false) ) )
  in
  {
    cs_mlmagic = scrut_is_mlmagic;
    cs_cpp_erased = scrut_is_cpp_erased;
    cs_magic = scrut_is_magic;
    cs_callee_ret_erased = scrut_callee_ret_erased;
    cs_typ = typ;
    cs_concrete = concrete_match_type;
    cs_pair = pair_g_opt;
    cs_pair_any_cast = needs_pair_any_cast;
  }

(** The pattern variables [ids] (innermost first) of a custom match's branch
    matching [r], at the types they are bound at: every one that is not a box
    or a list retyped as erased where the pair is read back as
    [pair<any, any>] ([fix_a_fired]), then recovered from the scrutinee's own
    type [scrut_ml_typ] and retyped for the dependent parameters of [ml_typ],
    the match's annotation. *)
let custom_branch_binders env ~fix_a_fired ~scrut_ml_typ ~ml_typ r ids' =
  let ids' =
    if fix_a_fired then
      List.map (fun (x, ty) ->
        let cpp_ty = cpp_of_ml_ir env ty in
        match cpp_ty with
        | Entity_application (g, (_ :: _), _) when is_prod_global g ->
          (x, Tdummy Ktype)
        | Entity_application (g, _, _) when is_list_global g ->
          (x, ty)
        | _ when Cpp_ir.Types.prints_as_any cpp_ty ->
          (x, ty)
        | _ ->
          (x, Tdummy Ktype))
        ids'
    else ids'
  in
  let ids' = recover_pattern_var_types_from_scrutinee ~ctor:r scrut_ml_typ ids' in
  let ids' = retype_dependent_params ml_typ ids' in
  ids'
