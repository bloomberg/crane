(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Inductive types: methods generated onto an inductive's struct, and the
    struct itself -- constructors, factories, conversions, accessors and the
    iterative destructor.

    Part of declaration generation: {!Gen_decls} includes this module after
    {!Gen_functions}, and {!Cpp_ind} calls {!gen_ind_header_v2} and
    {!gen_record_methods} to turn an inductive or an eponymous record into a
    CppIR struct (or enum).  Methods are generated ahead of the files
    ({!generate_method_ahead}) and taken from {!methods_ahead} when the struct
    is built; their bodies, like every type and conversion translation
    produces, are MiniCpp until the struct takes them. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Translation
open Plan_templates
open Gen_context
open Gen_functions

module IntSet = Escape.IntSet

(** Replace [this] in an expression that a method returns with
    [shared_from_this()] of [inner_ty], recursing into lambdas and calls: a
    raw [this] cannot convert to the [shared_ptr] the return type expects. *)
let rec replace_return_this_expr inner_ty = function
  | CPPthis -> CPPshared_from_this inner_ty
  | CPPlambda l ->
    CPPlambda (map_lambda (replace_return_this_stmt inner_ty) Fun.id l)
  | CPPfun_call (_, f, args) ->
    CPPfun_call
      (call_opaque, replace_return_this_expr inner_ty f,
        map_args (replace_return_this_expr inner_ty) args )
  | e -> e

(** Statement-level counterpart of {!replace_return_this_expr}: recurses into
    if/switch/match branches to replace [return this] with [shared_from_this]. *)
and replace_return_this_stmt inner_ty = function
  | Sreturn (Some e) -> Sreturn (Some (replace_return_this_expr inner_ty e))
  | Sif (cond, then_stmts, else_stmts) ->
    Sif
      ( cond,
        List.map (replace_return_this_stmt inner_ty) then_stmts,
        List.map (replace_return_this_stmt inner_ty) else_stmts )
  | Scustom_case (ty, scrut, tys, brs, tag) ->
    Scustom_case
      ( ty,
        scrut,
        tys,
        List.map
          (fun (binds, br_ty, stmts) ->
            (binds, br_ty, List.map (replace_return_this_stmt inner_ty) stmts) )
          brs,
        tag )
  | Sswitch (scrut, ind, brs, default) ->
    Sswitch
      ( scrut,
        ind,
        List.map
          (fun (ctor, stmts) ->
            (ctor, List.map (replace_return_this_stmt inner_ty) stmts) )
          brs,
        Option.map (List.map (replace_return_this_stmt inner_ty)) default )
  | Smatch (scrut, branches, default) ->
    Smatch
      ( scrut,
        List.map
          (fun br ->
            { br with
              smb_body =
                List.map (replace_return_this_stmt inner_ty) br.smb_body
            })
          branches,
        Option.map (List.map (replace_return_this_stmt inner_ty)) default )
  | Sexpr e -> Sexpr (replace_return_this_expr inner_ty e)
  | s -> s

(** Prevent dangling [this] in by-value lambda captures.

    When a methodified function contains a by-value lambda that references
    [this], the lambda may escape the method scope (returned through
    [option], [pair], record, etc.).  The raw [this] pointer dangles once
    the caller's [shared_ptr] is released.

    Fix: bind [shared_from_this()] to a local [_self] at the top of the
    method body, then replace [CPPthis] inside every by-value lambda body
    with [CPPvar "_self"].  The lambda's [=] capture picks up [_self] as
    a [shared_ptr] copy that keeps the object alive.  The outer method
    body keeps raw [CPPthis] for direct method calls (safe because the
    method is invoked on a live object). *)
let replace_this_in_lambdas ?receiver self_type stmts =
  let self_id = Id.of_string "_self" in
  (* Check if CPPthis or CPPshared_from_this appears in an expression. *)
  let rec expr_has_this = function
    | CPPthis | CPPshared_from_this _ -> true
    | e ->
      let found = ref false in
      ignore (map_expr (fun e' ->
        if expr_has_this e' then found := true; e') (fun s -> s) Fun.id e);
      !found
  in
  (* Check if CPPthis or CPPshared_from_this appears in statements. *)
  let rec stmt_has_this = function
    | s ->
      let found = ref false in
      ignore (map_stmt
        (fun e -> if expr_has_this e then found := true; e)
        (fun s' -> if stmt_has_this s' then found := true; s')
        Fun.id s);
      !found
  in
  let stmts_have_this stmts = List.exists stmt_has_this stmts in
  (* Check if any by-value lambda in the method body captures this. *)
  let rec lambda_captures_this_expr = function
    | CPPlambda {cl_body = body; cl_capture = Closure; _} -> stmts_have_this body
    | e ->
      let found = ref false in
      ignore (map_expr (fun e' ->
        if lambda_captures_this_expr e' then found := true; e')
        (fun s ->
          if lambda_captures_this_stmt s then found := true; s)
        Fun.id e);
      !found
  and lambda_captures_this_stmt s =
    let found = ref false in
    ignore (map_stmt
      (fun e -> if lambda_captures_this_expr e then found := true; e)
      (fun s' -> if lambda_captures_this_stmt s' then found := true; s')
      Fun.id s);
    !found
  in
  let needs_self = List.exists lambda_captures_this_stmt stmts in
  if not needs_self then stmts
  else
    (* Determine whether _self is a value type (non-enum).
       Coinductives and regular inductives are both value types. *)
    let is_value_self =
      match self_type with
      | Tglob (self_ref, _, _) -> not (is_enum_inductive self_ref)
      | _ -> false
    in
    (* For value-type methods, the loopifier uses "_self" as the name for the
       receiver pointer (const T *_self = this / _f._self).  Using the same
       name for the value copy would cause a redefinition conflict in loopified
       methods.  Use "_self_val" for the value copy to avoid the clash. *)
    let self_id = if is_value_self then Id.of_string "_self_val" else self_id in
    (* Substitute CPPthis and CPPshared_from_this → CPPvar self_id inside
       by-value lambda bodies.  For value-type _self_val, also collapse
       CPPderef(CPPthis) → CPPvar self_id to avoid dereferencing a value. *)
    let rec subst_expr = function
      | CPPderef (CPPthis | CPPshared_from_this _) when is_value_self ->
        CPPvar self_id
      | CPPthis | CPPshared_from_this _ -> CPPvar self_id
      | e -> map_expr subst_expr subst_stmt Fun.id e
    and subst_stmt s =
      map_stmt subst_expr subst_stmt Fun.id s
    in
    (* A closure taking the receiver by move takes the copy by move. *)
    let copy_moved l =
      match receiver with
      | Some r when List.exists (Id.equal r) l.cl_moved ->
        {l with cl_moved = List.sort Id.compare (self_id :: List.filter (fun x -> not (Id.equal x r)) l.cl_moved)}
      | _ -> l
    in
    let rec walk_expr = function
      | CPPlambda ({cl_capture = Closure; _} as l) ->
        CPPlambda (copy_moved (map_lambda subst_stmt Fun.id l))
      | e -> map_expr walk_expr walk_stmt Fun.id e
    and walk_stmt s =
      map_stmt walk_expr walk_stmt Fun.id s
    in
    let self_expr, self_ty =
      if is_value_self then
        (CPPderef CPPthis, Declare (self_type, None))
      else
        (CPPshared_from_this self_type, Declare (Tshared_ptr self_type, None))
    in
    let self_binding = Sasgn (self_id, self_ty, self_expr) in
    self_binding :: List.map walk_stmt stmts

(** Whether an expression of a method body is [shared_from_this()]: itself,
    or inside a lambda's body or a call. *)
let rec expr_has_shared_from_this : Cpp_ir.Lowered.Expr.t -> bool = function
  | Shared_from_this _ -> true
  | Lambda {body; _} -> List.exists stmt_has_shared_from_this body
  | Call (_, f, args) -> expr_has_shared_from_this f || List.exists expr_has_shared_from_this args
  | _ -> false

(** Statement-level counterpart of {!expr_has_shared_from_this}: checks whether
    any statement in a method body contains [shared_from_this()]. *)
and stmt_has_shared_from_this : Cpp_ir.Lowered.Stmt.t -> bool = function
  | Return (Some e) -> expr_has_shared_from_this e
  | Expression e -> expr_has_shared_from_this e
  | If {then_; else_; _} ->
    List.exists stmt_has_shared_from_this then_ || List.exists stmt_has_shared_from_this else_
  | Custom_match {branches; _} ->
    List.exists (fun (b : _ Cpp_ir.Stmt.Custom_match.branch) -> List.exists stmt_has_shared_from_this b.body) branches
  | Switch {branches; default; _} ->
    List.exists (fun (_, stmts) -> List.exists stmt_has_shared_from_this stmts) branches
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Match (_, branches, default) ->
    List.exists (fun (b : _ Cpp_ir.Stmt.Match.branch) -> List.exists stmt_has_shared_from_this b.body) branches
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Bind_variable (_, _, e) -> expr_has_shared_from_this e
  | _ -> false

(** What a method is generated under, settled before its body: the
    function's type and body with its variables renumbered so the
    inductive's come first, the variables of its own and their names, its
    return type, its parameters and the environment naming them, and the head
    before {!method_head} decides which of its own variables it keeps. *)
type method_scope = {
  ms_ty : ml_type;  (** The function's type, renumbered. *)
  ms_ret_ty : ml_type;  (** Its ML return type, renumbered. *)
  ms_body : ml_ast;  (** Its body, renumbered. *)
  ms_all_tvars : int list;
      (** The variables of the type before renumbering, sorted. *)
  ms_remap : int -> int;
      (** The renumbering, from a variable of the function's scheme to its
          position after the inductive's. *)
  ms_extra_tvars_orig : int list;
      (** The function's own variables, the ones the inductive does not bind,
          numbered as in its scheme. *)
  ms_extra_tvar_names : Id.t list;
      (** The C++ names of {!ms_extra_tvars_orig}, in the same order. *)
  ms_subst_extra_tvars : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t;
      (** Spells the function's own variables in a C++ type by their names. *)
  ms_method_ns : Ref.User.Set.t;
      (** The inductive alone: the scope its types are converted in, so a
          recursive occurrence inside a container is spelled as the struct's
          fields spell it. *)
  ms_strip_self_ptr : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t;
      (** Removes the [shared_ptr] around a value-type inductive, which a
          method takes and returns by value. *)
  ms_ret_cpp : Cpp_ir.Lowered.Type.t;
      (** The C++ return type, before {!method_head} erases the variables it
          alone mentions. *)
  ms_ids_with_types : (ml_ident * ml_type) list;
      (** The declared parameters, innermost first. *)
  ms_inner_body : ml_ast;  (** The body under those parameters. *)
  ms_env : env;  (** The environment naming the parameters, renamed apart. *)
  ms_method_owned_flags : bool list;
      (** Whether each parameter is owned, innermost first. *)
  ms_this_arg_id : Id.t option;
      (** The parameter that becomes the receiver [this]. *)
  ms_params : (Id.t * Cpp_ir.Lowered.Type.t) list;
      (** The C++ parameters: the runtime ones other than the receiver, each
          wrapped by ownership, a callable as an [F &&]. *)
  ms_passing : Callable_abi.passing list;
      (** How each of {!ms_params} is passed. *)
  ms_fun_params : (Id.t * Callable_abi.kind * Id.t) list;
      (** The callable parameters generalised to a template parameter: the
          parameter, its [Callable_declared] constraint and the template
          parameter's name. *)
  ms_template_params : Cpp_ir.Lowered.phase Cpp_ir.Template.parameters;
      (** The template parameters before {!method_head} drops any: the
          instances, then the function's own variables, then the
          callables. *)
  ms_minted : (Id.t * Callable_abi.minted) list;
      (** What each of {!ms_template_params} was made for: a dictionary, a
          variable of the function's scheme, or a callable parameter. *)
  ms_deduced_callables : Param_pos.orig Param_pos.pos list;
      (** The declared positions of the callables deduced as an [F &&]. *)
}

(** [method_scope name vars (func_ref, body, ty, this_pos)] settles the scope
    of the method made of the function [func_ref], of body [body] and type
    [ty], in the inductive [name] whose template variables are [vars];
    [this_pos] is the 0-based index of the parameter that becomes [this]. *)
let method_scope name vars (func_ref, body, ty, this_pos) =
  (* Promotion moves a function into a struct; it does not change what the
     function returns.  The mode is read off the codomain here exactly as it is
     for a function left at top level -- otherwise an [itree] body reached as a
     method would be desugared sequentially while the signature it is being
     given says [shared_ptr<ITree<_>>]. *)
  with_itree_mode_for ty @@ fun () ->
  let num_ind_vars = List.length vars in
  let _, ret_ty = get_args_and_ret [] ty in
  (* The function's variables renumbered so the inductive's come first and
     its own after them ({!Method_registry.renumbering}), the positions
     convert_ml_type_to_cpp_type maps. *)
  let renumbering = Method_registry.renumbering ~num_ind_vars ~this_pos ty in
  let extra_tvars_orig = renumbering.extra in
  let remap_ml_tvar = renumbering.rename in
  let all_tvars = List.sort compare (collect_tvars [] ty) in
  let ty = Method_registry.renumber_type renumbering ty in
  let ret_ty = Method_registry.renumber_type renumbering ret_ty in
  let body = Method_registry.renumber_body renumbering body in
  let extra_remap = List.mapi (fun i orig -> (orig, num_ind_vars + 1 + i)) extra_tvars_orig in
  (* After remapping, extra tvars are at positions num_ind_vars+1,
     num_ind_vars+2, ... *)
  let extra_tvars = List.map snd extra_remap in
  let extra_tvar_names = List.mapi (fun i _ -> tvar_id (i + 1)) extra_tvars in
  let extra_tvar_map = List.combine extra_tvars extra_tvar_names in
  let subst_extra_tvars = make_subst_extra_tvars_ir num_ind_vars extra_tvar_map in

  (* For type conversion in method contexts, use ns = {name} so that
     self-references INSIDE container types get shared_ptr wrapping
     (matching how struct fields are defined).  Then strip the top-level
     shared_ptr for the method's own type (value-type inductives are
     passed/returned by value, not by shared_ptr). *)
  let method_ns = Ref.User.Set.singleton name in
  let rec strip_self_ptr (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
    match ty with
    | Shared_pointer (Entity_application (g, _, _) as inner) when not (is_enum_inductive g) -> inner
    | Entity_application (r, args, es) -> Entity_application (r, List.map strip_self_ptr args, es)
    | Function (args, ret) -> Function (List.map strip_self_ptr args, strip_self_ptr ret)
    | Reference (k, t) -> Reference (k, strip_self_ptr t)
    | Const t -> Const (strip_self_ptr t)
    | _ -> ty
  in
  let strip_top_level_self_ptr ty = strip_self_ptr ty in
  let ret_cpp = cpp_ir_of_ml_type (empty_env ()) ~ns:method_ns vars ret_ty in
  let ret_cpp = strip_top_level_self_ptr ret_cpp in
  let ret_cpp = subst_extra_tvars ret_cpp in

  (* Collect lambda parameters and build environment for de Bruijn lookup.
     push_vars' may rename duplicate parameters (e.g., two params named 't'
     become 't', 't0').

     The renamed ids (all_ids) are used consistently for both the
     environment, so gen_expr/gen_stmts produce correct variable references,
     and the C++ method signature, so parameter names match what the body
     references.  Signing with the original names would declare
     [void method(tree t)] around a body reading [t0].

     Only as many as the type declares, as for a function: a lambda beyond
     them -- under a result that is an alias of a function type -- is the
     closure the method returns, which is how its callers, reading the
     type, call it. *)
  (* A body with fewer lambdas than the type has domains -- [tree_to_adder :
     tree -> nat -> nat] matching and returning closures -- is eta-expanded,
     as a function's is. *)
  let ids_with_types, inner_body = declared_parameters ty body in
  let ids_converted, typeclass_temps =
    promote_typeclass_params
      (List.map (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty)) ids_with_types)
  in
  let all_ids, env = push_vars' ids_converted (empty_env ()) in
  reset_env_types ();
  push_parameters env all_ids;
  (* Infer owned/borrowed for method parameters. Note: method 'this' is always
     borrowed (const method). *)
  let n_method_params = List.length ids_with_types in
  let method_owned_flags = Ownership.read_off ids_with_types inner_body in

  (* Extract 'this' argument at this_pos - use renamed ids for consistency with
     body *)
  let ids_normal_order = List.rev all_ids in
  let this_arg_id_opt, param_ids_with_pos =
    Common.extract_at_pos
      this_pos
      (List.mapi (fun i (id, ty) -> (id, ty, i)) ids_normal_order)
  in
  let this_arg_id = Option.map (fun (id, _, _) -> id) this_arg_id_opt in
  let param_ids_with_pos =
    List.filter
      (fun (_, ty, _) ->
        (* An instance is either promoted to a template parameter or skipped
           outright; either way it is not among the arguments a call passes,
           and {!Ml_type_util.ml_type_is_instance} is where both cases are
           recognised -- a skipped class is a [ConstRef] mapped to the empty
           string, which [is_typeclass_type] alone does not see. *)
        Ml_type_util.is_runtime_binder_type ty && not (Ml_type_util.ml_type_is_instance ty) )
      param_ids_with_pos
  in

  (* Build owned flag lookup for non-this params. ids_normal_order is
     outermost-first. de Bruijn index of element i in normal order =
     n_method_params - i. method_owned_flags[db - 1] gives the owned flag. *)
  let get_param_owned_flag normal_order_idx =
    let db = n_method_params - normal_order_idx in
    match List.nth_opt method_owned_flags (db - 1) with
    | Some b -> b
    | None -> false
  in

  (* Convert params to C++ types.  Use method_ns so that self-references
     inside container types get shared_ptr (matching struct field types).
     Strip top-level shared_ptr since value-type params are bare values. *)
  (* A callable parameter is generalised to [F &&] as a free function's is:
     not where a self-call passes something else for it, nor where a closure
     holds on to it. *)
  let ungeneralised =
    ungeneralised_callable_params ~self_ref:func_ref
      ~suspended:(Table.is_coinductive_type ret_ty) n_method_params inner_body
  in
  let params_with_idx =
    List.mapi
      (fun i (id, ty, orig_idx) ->
        let cpp_ty = cpp_ir_of_ml_type env ~ns:method_ns vars ty in
        let cpp_ty = strip_top_level_self_ptr cpp_ty in
        let cpp_ty = subst_extra_tvars cpp_ty in
        let owned = get_param_owned_flag orig_idx in
        (id, cpp_ty, i, owned, not (Escape.IntSet.mem orig_idx ungeneralised)) )
      param_ids_with_pos
  in

  (* Extract function-typed parameters for template params *)
  let fun_params =
    List.filter_map
      (fun (id, (cpp_ty : Cpp_ir.Lowered.Type.t), i, _, generalised) ->
        match cpp_ty with
        | Function (dom, cod) when generalised ->
          let cod = if is_cpp_unit_type_ir cod then (Void : Cpp_ir.Lowered.Type.t) else cod in
          Some (id, (Callable_declared (dom, cod) : Callable_abi.kind), fun_tparam_id i)
        | _ -> None )
      params_with_idx
  in

  (* Build template params *)
  let extra_type_params =
    List.map (fun name -> ((Typename : Callable_abi.kind), name)) extra_tvar_names
  in
  let fun_template_params =
    List.map (fun (_, tt, fname) -> (tt, fname)) fun_params
  in
  (* The instances come first, as they do for a free function: a call site
     spells the same list in the same order. *)
  let template_params =
    Legacy_minicpp_to_cpp_ir.lower_template_parameters (List.map (fun (tt, id, _, _) -> (tt, id)) typeclass_temps)
    @ extra_type_params
    @ fun_template_params
  in

  (* The declared positions of the callables deduced as an [F &&], among the
     function's binders in source order. *)
  let deduced_callables =
    let binder_tys = List.rev_map snd ids_with_types in
    List.filter_map
      (fun ((_, (cpp_ty : Cpp_ir.Lowered.Type.t), _, _, generalised), (_, _, orig_idx)) ->
        match cpp_ty with
        | Function _ when generalised -> Param_pos.of_source_index binder_tys orig_idx
        | _ -> None )
      (List.combine params_with_idx param_ids_with_pos)
  in

  (* Build final params with proper wrapping. Use escape analysis to determine
     owned vs borrowed: owned params are passed by value (for move semantics),
     borrowed params are passed by const ref. This matches gen_dfun's logic to
     ensure forward declarations and definitions agree. *)
  let params =
    List.map2
      (fun (id, (cpp_ty : Cpp_ir.Lowered.Type.t), i, owned, generalised) (_, core, _) ->
        let wrapped : Cpp_ir.Lowered.Type.t =
          match cpp_ty with
          | Function _ when generalised -> Reference (Forwarding, Variable (Named (fun_tparam_id i)))
          | _ -> wrap_param_by_ownership_ir ~is_owned:owned ~core cpp_ty
        in
        (id, wrapped) )
      params_with_idx param_ids_with_pos
  in
  let passing =
    List.map2 (fun (_, ty) (_, _, _, owned, _) -> param_passing_ir ~owned ty) params params_with_idx
  in

  {
    ms_ty = ty;
    ms_ret_ty = ret_ty;
    ms_body = body;
    ms_all_tvars = all_tvars;
    ms_remap = remap_ml_tvar;
    ms_extra_tvars_orig = extra_tvars_orig;
    ms_extra_tvar_names = extra_tvar_names;
    ms_subst_extra_tvars = subst_extra_tvars;
    ms_method_ns = method_ns;
    ms_strip_self_ptr = strip_top_level_self_ptr;
    ms_ret_cpp = ret_cpp;
    ms_ids_with_types = ids_with_types;
    ms_inner_body = inner_body;
    ms_env = env;
    ms_method_owned_flags = method_owned_flags;
    ms_this_arg_id = this_arg_id;
    ms_params = params;
    ms_passing = passing;
    ms_fun_params = fun_params;
    ms_template_params = template_params;
    ms_minted =
      List.mapi (fun k (_, id, _, _) -> (id, Callable_abi.Instance_param k)) typeclass_temps
      @ List.map2 (fun name orig -> (name, Callable_abi.Scheme_param orig)) extra_tvar_names extra_tvars_orig
      @ List.filter_map
          (fun (_, (cpp_ty : Cpp_ir.Lowered.Type.t), i, _, generalised) ->
            match cpp_ty with
            | Function _ when generalised -> Some (fun_tparam_id i, Callable_abi.Callable_param i)
            | _ -> None )
          params_with_idx;
    ms_deduced_callables = deduced_callables;
  }

(** Whether a type mentions the template parameter [name] anywhere. *)
let cpp_type_has_tvar name =
  exists_cpp_type (function
    | Tvar (Tv_index (_, Some n) | Tv_named n) -> Id.equal n name
    | _ -> false )

(** {!cpp_type_has_tvar} over a CppIR type. *)
let cpp_type_has_tvar_ir name =
  Cpp_ir.Children.exists_type (fun (t : Cpp_ir.Lowered.Type.t) ->
      match t with
      | Variable (Index (_, Some n) | Named n) -> Id.equal n name
      | _ -> false )

(** The head of the method [s] is the scope of, with which of its own
    variables it keeps decided: its template parameters, its return type, the
    variables of its own the return type alone mentions, which it erases
    there, and those it drops, each with the variable of the function's
    scheme it stood for.  Decided from the signature and the body's
    annotations, so before the body is generated. *)
type method_head = {
  mh_tparams : Cpp_ir.Lowered.phase Cpp_ir.Template.parameters;
      (** The template parameters the method keeps: instances, its own
          variables that something still names, callables. *)
  mh_ret : Cpp_ir.Lowered.Type.t;
      (** The C++ return type, with {!mh_return_only} erased to [std::any]. *)
  mh_return_only : Id.Set.t;
      (** Its own variables that only the return type mentions. *)
  mh_dropped : (int * Id.t) list;
      (** Its own variables it does not quantify, each with the variable of
          the function's scheme it stood for. *)
}

(** [method_head vars s] decides the {!method_head} of the method whose scope
    is [s], in an inductive whose template variables are [vars]. *)
let method_head vars s =
  let {
    ms_extra_tvars_orig = extra_tvars_orig;
    ms_extra_tvar_names = extra_tvar_names;
    ms_subst_extra_tvars = subst_extra_tvars;
    ms_method_ns = method_ns;
    ms_strip_self_ptr = strip_top_level_self_ptr;
    ms_ret_cpp = ret_cpp;
    ms_inner_body = inner_body;
    ms_params = params;
    ms_fun_params = fun_params;
    ms_template_params = template_params;
    _
  } = s in
  (* Filter out phantom extra template params: if an extra tvar name doesn't
     appear in any param type or the return type, it's phantom (e.g., a killed
     inductive type arg) and shouldn't be a template param. *)
  let extra_tvar_name_set =
    List.fold_left (fun s n -> Id.Set.add n s) Id.Set.empty extra_tvar_names
  in
  (* The body counts too.  A tvar the signature never mentions is usually one
     erasure killed outright, but a local binding can still be declared at it
     -- the result of a trigger is an index of the event type, so it has no
     spelling but the variable's own -- and dropping the parameter leaves the
     body naming something that is no longer declared.  Read off the body's
     own annotations as C++ spells them, and the callables the head deduces,
     so the head is decided without generating the body. *)
  let body_names =
    let annotations = ref [] in
    ignore
      (Mlutil.ast_map_types
         (fun t ->
           annotations := t :: !annotations;
           t )
         inner_body );
    (* A hole names no variable; it is declined rather than converted. *)
    let declined = Mlutil.map_ml_type (function Thole _ -> Tunknown | t -> t) in
    let annotations =
      with_type_vars (vars @ extra_tvar_names) (fun () ->
          List.rev_map
            (fun t ->
              subst_extra_tvars
                (strip_top_level_self_ptr (cpp_ir_of_ml_type (empty_env ()) ~ns:method_ns vars (declined t))) )
            !annotations )
    in
    let constraints =
      List.concat_map
        (fun (_, (tt : Callable_abi.kind), _) -> match tt with Callable_declared (d, c) -> c :: d | _ -> [])
        fun_params
    in
    fun name -> List.exists (cpp_type_has_tvar_ir name) (constraints @ annotations)
  in
  (* An extra tvar the return type is alone in mentioning is a dead letter.
     Nothing deduces it -- the receiver carries only the inductive's own
     parameters, and no value parameter names it -- and the body cannot honour
     it either, since the body never names it: whatever the body builds, it
     builds at one fixed type.  Quantifying it declares a method no call can
     name; the honest spelling is the erased one, which is also what the index
     of an event family reaches C++ as everywhere else. *)
  let return_only_tvars =
    List.filter_map
      (fun (_tt, tname) ->
        if
          Id.Set.mem tname extra_tvar_name_set
          && cpp_type_has_tvar_ir tname ret_cpp
          && (not (List.exists (fun (_, pty) -> cpp_type_has_tvar_ir tname pty) params))
          && not (body_names tname)
        then Some tname
        else None )
      template_params
  in
  let return_only_set =
    List.fold_left (fun s n -> Id.Set.add n s) Id.Set.empty return_only_tvars
  in
  let ret_cpp =
    if Id.Set.is_empty return_only_set then ret_cpp
    else
      Cpp_ir.Types.map
        (fun (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
          match t with
          | Variable (Index (_, Some n) | Named n) when Id.Set.mem n return_only_set -> Any
          | t -> t )
        ret_cpp
  in
  let template_params =
    List.filter (fun (_tt, tname) ->
      if not (Id.Set.mem tname extra_tvar_name_set) then true
      else if Id.Set.mem tname return_only_set then false
      else
        cpp_type_has_tvar_ir tname ret_cpp
        || List.exists (fun (_, pty) -> cpp_type_has_tvar_ir tname pty) params
        || body_names tname)
    template_params
  in
  let surviving_names =
    List.fold_left (fun s (_, n) -> Id.Set.add n s) Id.Set.empty template_params
  in
  {
    mh_tparams = template_params;
    mh_ret = ret_cpp;
    mh_return_only = return_only_set;
    mh_dropped =
      List.filter
        (fun (_, n) -> Id.Set.mem n extra_tvar_name_set && not (Id.Set.mem n surviving_names))
        (List.combine extra_tvars_orig extra_tvar_names);
  }

(** The callable plan of the method [func_ref] whose scope is [s] and head
    [h]: a parameter for one of its own variables declares the function's
    variable it was renumbered from ({!method_scope}). *)
let method_plan func_ref s h =
  let scheme = Mlutil.reference_scheme func_ref in
  Callable_abi.of_head ~minted:s.ms_minted
    ~omitted:(Translation_support.type_arg_omission func_ref)
    ~deduced_callables:s.ms_deduced_callables ~passing:s.ms_passing
    ~receiver:
      { dropped =
          List.filter_map (fun (i, _) -> Option.bind scheme (fun sc -> Scheme.Var.of_tvar sc i)) h.mh_dropped;
        dropped_names = List.map snd h.mh_dropped;
        params = List.map snd s.ms_params;
        ret = h.mh_ret;
        return_only = Id.Set.elements h.mh_return_only }
    ~callee:func_ref ~scheme h.mh_tparams

(** [plan_method name vars candidate] is the callable plan of the method
    made of [candidate] in the inductive [name] whose variables are [vars],
    as generating it would plan it, without generating its body. *)
let plan_method name vars ((func_ref, _, ty, _) as candidate) =
  let s = method_scope name vars candidate in
  with_itree_mode_for ty @@ fun () -> method_plan func_ref s (method_head vars s)

(** The head of the method [func_ref] whose scope is [s]: its plan's, which
    was made before anything was generated, as its template parameters, its
    return type, the variables the return type alone mentions, and the names
    of the variables it drops.  Under [CRANE_CHECK_IR] the head is decided
    again ({!method_head}) and checked against the plan. *)
let planned_method_head func_ref vars s =
  let abi = Callable_abi.planned func_ref in
  if Probe.checking () then Callable_abi.check (method_plan func_ref s (method_head vars s));
  match Callable_abi.receiver abi with
  | Some r ->
    ( Cpp_ir_to_legacy_minicpp.template_parameters (Callable_abi.declared_head abi),
      Cpp_ir_to_legacy_minicpp.ty r.ret,
      Id.Set.of_list r.return_only,
      r.dropped_names )
  | None ->
    CErrors.anomaly
      Pp.(str "the method " ++ GlobRef.print func_ref ++ str " was planned as a function.")

(** Generate a single method for an inductive type from a method candidate:
    its body, generated under {!method_scope} and its planned head. *)
let generate_method name vars ((func_ref, _, ty, this_pos) as candidate) =
  let s = method_scope name vars candidate in
  (* Promotion moves a function into a struct; it does not change what the
     function returns: see {!method_scope}. *)
  with_itree_mode_for ty @@ fun () ->
  let tparams, ret, return_only, dropped_names = planned_method_head func_ref vars s in
  let func_name = Common.id_of_global Term func_ref in
  let {
    ms_ty = ty;
    ms_ret_ty = ret_ty;
    ms_body = body;
    ms_all_tvars = all_tvars;
    ms_remap = remap_ml_tvar;
    ms_extra_tvar_names = extra_tvar_names;
    ms_method_ns = method_ns;
    ms_ret_cpp = ret_cpp;
    ms_ids_with_types = ids_with_types;
    ms_inner_body = inner_body;
    ms_env = env;
    ms_method_owned_flags = method_owned_flags;
    ms_this_arg_id = this_arg_id;
    ms_params = params;
    _
  } = s in
  let ret_cpp = Cpp_ir_to_legacy_minicpp.ty ret_cpp in
  let params = List.map (fun (x, t) -> (x, Cpp_ir_to_legacy_minicpp.ty t)) params in
  (* Suspended at its constructors, and whole only where it calls itself
     outside all of them: see [cofix_wrap] in [gen_dfun]. *)
  let is_cofix_method =
    Translation_support.suspends_whole func_ref ret_ty (snd (collect_lams body))
  in
  let method_k x =
    if is_cofix_method then
      suspend_whole
        ~cpp_of:(convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Ref.User.Set.singleton name) vars)
        ~cod:ret_cpp ret_ty x
    else
      Sreturn (Some x)
  in
  (* Generate the method body, owning its owned parameters.  The de Bruijn
     environment has parameters in reverse order: ids_normal_order has
     outermost-first, push_vars' reverses them. *)
  begin_body ~owner:func_ref ();
  let method_n_params = List.length ids_with_types in
  (* method_owned_flags[i] corresponds to de Bruijn index i+1.
     db index i+1 maps to ids_with_types[i] (innermost first, the order
     push_vars' puts at the front of the environment).
     Only track ownership for non-trivial types (inductives). *)
  let owned_params =
    Translation_support.owned_parameters (List.length method_owned_flags)
      ~owned:(fun i ->
        (* The receiver at [this_pos] is the const [this], borrowed: a move of
           it copies, and a reuse arm would try to consume it via v_mut() on a
           const method.  Its closures own the copy they capture
           ([closures_copy]).  [this_pos] counts the parameters outermost
           first, [i] innermost first. *)
        (not (this_arg_id <> None && i = method_n_params - 1 - this_pos))
        && Translation_support.declared_by_value
             (List.assoc_opt (Common.get_db_name (i + 1) env) params)
             ~summary:(List.nth method_owned_flags i) )
      ~declared:(fun i -> List.assoc_opt (Common.get_db_name (i + 1) env) params)
      ~ty:(fun i -> snd (List.nth ids_with_types i))
  in
  (* The receiver becomes [this]; a closure reading it captures a copy of
     the object ({!replace_this_in_lambdas}), which the closures own. *)
  let closures_copy = if this_arg_id <> None then [method_n_params - this_pos] else [] in
  (* Where it is lowered as a machine with a stack of frames, the frames it
     saves are planned with the body: certainly, or perhaps. *)
  let resumes, certain =
    match
      Control_to_cpp_ir.method_resumes func_ref ~inductive:name ~receiver:this_pos
        ~depth:(List.length (fst env))
    with
    | Some (resumes, certain) -> (Some resumes, Some certain)
    | None -> (None, None)
  in
  (* The scope covers both the inductive's type vars and the extra ones, so
     that gen_expr/eta_fun convert Tvars to the named C++ types the method
     body expects (e.g. recursive calls carry type args).  The return type is
     exposed to the body as [gen_dfun] exposes a function's, so a result
     recovered from a box is recovered at it. *)
  let stmts =
    with_cpp_return_type (Some ret_cpp) @@ fun () ->
    with_type_vars (vars @ extra_tvar_names) (fun () ->
        (* Include all local value-type inductives with recursive fields in the
           method ns.  This ensures that when the method body constructs or
           manipulates containers of recursive types (e.g. List<tree>), the
           type arguments get shared_ptr wrapping to match struct field
           types. *)
        with_method_ns_for_locals ~base:method_ns (fun () ->
            with_region ~owned:owned_params ~copied:closures_copy ?resumes ?certain inner_body (fun () ->
                gen_stmts env method_k inner_body ) ) )
  in
  (* Add type args to recursive self-calls. Inside fixpoint bodies, the
     extraction produces a self reference whose variables stand for themselves
     and are written nowhere ({!Mlutil.self_reference}). When the function is a
     method, the recursive call needs
     explicit template args for non-deducible params. Replace CPPglob(func_ref,
     []) with CPPglob(func_ref, all_type_args).

     The type args must be in the ORIGINAL tys order (matching the
     inductive's variable positions {!Cpp_names.method_type_args} filters out
     at the call site, {!Cpp_state.lookup_method_ind_tvar_positions}).
     Position i in tys
     corresponds to Tvar (i+1) in the original ML type. After remapping, Tvar
     (i+1) → remap_ml_tvar(i+1). We construct the C++ type arg from
     extended_vars at that remapped position. *)
  let extended_vars = vars @ extra_tvar_names in
  let all_method_type_args =
    List.filter_map
      (fun orig_tvar_idx ->
        let remapped = remap_ml_tvar orig_tvar_idx in
        if remapped - 1 >= List.length extended_vars then
          None
        else
          let name = List.nth extended_vars (remapped - 1) in
          Some (named_tvar name) )
      all_tvars
  in
  let stmts =
    if all_method_type_args <> [] then
      let self_call_with_tys = mk_cppglob func_ref all_method_type_args in
      List.map (glob_subst_stmt func_ref self_call_with_tys) stmts
    else
      stmts
  in
  let stmts =
    match this_arg_id with
    | Some id ->
      (* For value-type methods, substitute with [CPPderef CPPthis] so that
         return positions produce a value copy rather than a raw pointer.
         For shared_ptr/coinductive methods, keep bare [CPPthis]. *)
      let this_expr =
        if not (Table.is_coinductive name) && not (is_enum_inductive name) then
          CPPderef CPPthis
        else CPPthis
      in
      List.map (var_subst_stmt id this_expr) stmts
    | None -> stmts
  in
  (* Replace [CPPthis] with [CPPshared_from_this] in return expressions.  When a
     method body returns or stores [this] in a position that expects [shared_ptr]
     (e.g. [return this;], [return std::make_pair(this, this);]), the raw pointer
     cannot convert to [shared_ptr].  Using [shared_from_this()] produces a valid
     [shared_ptr] from the raw pointer.  Only applied when the return type
     contains [shared_ptr] (e.g. [shared_ptr<T>], [pair<shared_ptr, shared_ptr>])
     to avoid replacing [this] in method calls that just forward the receiver. *)
  (* Compute self_type unconditionally: both the return-this and the
     lambda-this passes need it. *)
  let self_type_args =
    List.map named_tvar vars
  in
  let self_type = Tglob (name, self_type_args, []) in
  let stmts =
    if contains_shared_ptr ret_cpp then
      List.map (replace_return_this_stmt self_type) stmts
    else stmts
  in
  (* Replace [CPPthis] inside by-value lambda bodies with a copy of the
     receiver bound at the top of the method ({!replace_this_in_lambdas}).
     When a method returns a closure that captures [this], the raw pointer
     would dangle once the receiver is gone; the closure holding its own copy
     keeps the value alive. *)
  let stmts = return_captures_by_value stmts in
  let stmts = replace_this_in_lambdas ?receiver:this_arg_id self_type stmts in
  (* Apply tvar_subst_stmt with the extended vars list (defined above).
     extended_vars covers positions 1..num_ind_vars (inductive vars) and
     num_ind_vars+1, num_ind_vars+2, etc. (extra vars) so tvar_subst_stmt can
     name them all correctly. *)
  (* A [tt] the method returns is dead where its result is not [unit] -- with
     the codomain read as a top-level function's is, a monad's unit included. *)
  let stmts =
    finish_fn_body
      (apply_unit_void (ml_type_is_void_call ty) ret_cpp)
      (List.map (tvar_subst_stmt extended_vars) stmts)
  in


  let no_pure = is_monadic_ml_type ret_ty in
  (* What the body generated does name.  A callee printed verbatim from its
     custom text names its type arguments, and the signature recorded on a
     call to it, only where the text spells them: not at all, here.  A method
     callee, this one's own self-call included, is written on its receiver
     with only the type arguments {!Cpp_names.method_type_args} keeps: the
     ones the receiver carries and the ones its head dropped are not. *)
  let stmt_has_tvar name stmts =
    let found = ref false in
    let rec on_type t =
      if cpp_type_has_tvar name t then found := true;
      t
    and on_expr = function
      | CPPglob (_, _, Some {ci_inline = Some _; _}) as e -> e
      | CPPfun_call (_, CPPglob (_, _, Some {ci_inline = Some _; _}), args) as e ->
        List.iter (fun a -> ignore (on_expr a)) (to_reversed args);
        e
      | CPPglob (r, tys, ci) as e when Cpp_names.lookup_method_this_pos r <> None ->
        ignore (Minicpp.map_expr on_expr on_stmt on_type (CPPglob (r, Cpp_names.method_type_args r tys, ci)));
        e
      | e -> Minicpp.map_expr on_expr on_stmt on_type e
    and on_stmt s = Minicpp.map_stmt on_expr on_stmt on_type s in
    List.iter (fun s -> ignore (on_stmt s)) stmts;
    !found
  in
  (* A variable the head drops must be one the body does not name either:
     the body would name a parameter no longer declared. *)
  if Probe.checking () then
    List.iter
      (fun name ->
        if stmt_has_tvar name stmts then
          Probe.violation "method head"
            Pp.(
              str "the body of " ++ GlobRef.print func_ref ++ str " names " ++ Id.print name
              ++ str ", which none of its annotations does" ) )
      dropped_names;
  (* The body still builds its value at the one type it knows; the signature
     now promises the erased one.  [crane_container_cast] is the conversion
     between the two, and it is the identity when they agree.

     A return type that erased away entirely needs nothing said: anything
     converts to [std::any] by boxing. *)
  let stmts =
    if Id.Set.is_empty return_only || ret = Tany then stmts
    else
      let rec cast_stmt s =
        match s with
        | Sreturn (Some e) -> Sreturn (Some (CPPcontainer_cast (ret, e, false)))
        | _ -> Minicpp.map_stmt (fun e -> e) cast_stmt (fun t -> t) s
      in
      List.map cast_stmt stmts
  in
  let phantom_name_set = Id.Set.of_list dropped_names in
  let rec strip_phantom_any_cast_expr e =
    let e = match e with
      | CPPany_cast (Tvar (Tv_index (_, Some name) | Tv_named name), inner) when Id.Set.mem name phantom_name_set ->
        strip_phantom_any_cast_expr inner
      | _ -> e
    in
    Minicpp.map_expr strip_phantom_any_cast_expr strip_phantom_any_cast_stmt (fun t -> t) e
  and strip_phantom_any_cast_stmt s =
    Minicpp.map_stmt strip_phantom_any_cast_expr strip_phantom_any_cast_stmt (fun t -> t) s
  in
  let stmts =
    if Id.Set.is_empty phantom_name_set then stmts
    else List.map strip_phantom_any_cast_stmt stmts
  in
  ( Fmethod
      {
        mf_name = func_name;
        mf_globref = Some func_ref;
        mf_tparams = tparams;
        mf_ret_type = ret;
        mf_params = params;
        mf_body = stmts;
        mf_receiver =
          Instance
            { this_pos;
              is_const = true;
              ref_qual = Rq_any;
              returns_field = Escape.returns_receiver_field ~this_pos body };
        mf_is_inline = false;
        mf_no_pure = no_pure;
        mf_constexpr = Undecided;
        mf_is_noexcept = false;
        mf_is_conversion = false;
        mf_binders = parameter_binders env params;
        mf_receiver_binder = Option.bind this_arg_id (local_binder env);
        mf_loop = None;
      },
    VPublic,
    SNoTag )

(** The methods generated ahead of the files, by the function each is made
    of, with the struct and variables it was generated for, and the helpers
    lifted out of its body. *)
let methods_ahead :
    ((GlobRef.t * Id.t list) * ((cpp_field * cpp_visibility * section_tag) * cpp_decl list)) list
    Ref.User.Tbl.t =
  Ref.User.Tbl.create 16

let () = State.on_reset State.Unit (fun () -> Ref.User.Tbl.reset methods_ahead)

(** [generate_method_ahead name vars candidate] generates the method made of
    [candidate] in the inductive [name], whose variables are [vars], before
    the files are rendered, records it in {!methods_ahead} with the helpers
    lifted out of its body, and returns those helpers. *)
let generate_method_ahead name vars ((func_ref, _, _, _) as candidate) =
  let generation = collecting_lifted (fun () -> generate_method name vars candidate) in
  Ref.User.Tbl.replace methods_ahead func_ref
    (((name, vars), generation)
     :: Option.default [] (Ref.User.Tbl.find_opt methods_ahead func_ref) );
  snd generation

(** [check_method_ahead name vars candidate] generates the method again and
    raises an anomaly unless it is the one {!generate_method_ahead}
    recorded.  Run under [CRANE_CHECK_IR], in the reverse order: the order
    methods are generated in must not change them. *)
let check_method_ahead name vars ((func_ref, _, _, _) as candidate) =
  let recorded =
    List.find_map
      (fun ((name', vars'), (field, _)) ->
        if globref_equal name name' && List.equal Id.equal vars vars' then Some field else None )
      (Option.default [] (Ref.User.Tbl.find_opt methods_ahead func_ref))
  in
  let again = fst (collecting_lifted (fun () -> generate_method name vars candidate)) in
  if not (Option.equal (fun a b -> compare a b = 0) recorded (Some again)) then
    CErrors.anomaly
      Pp.(str "Crane: the method " ++ GlobRef.print func_ref
          ++ str " was generated differently in reverse order.")

(** [gen_single_method name vars candidate] is the method made of
    [candidate] in the inductive [name] whose variables are [vars], as
    generated ahead of the files ({!generate_method_ahead}), its helpers
    lifted again into the generation that takes it.  Under [CRANE_CHECK_IR]
    it is generated again and compared. *)
let gen_single_method name vars ((func_ref, _, _, _) as candidate) =
  match
    List.find_map
      (fun ((name', vars'), g) ->
        if globref_equal name name' && List.equal Id.equal vars vars' then Some g else None )
      (Option.default [] (Ref.User.Tbl.find_opt methods_ahead func_ref))
  with
  | Some (field, lifted) ->
    relift lifted;
    if Probe.checking ()
       && compare field (fst (collecting_lifted (fun () -> generate_method name vars candidate))) <> 0
    then
      CErrors.anomaly
        Pp.(str "Crane: the method " ++ GlobRef.print func_ref
            ++ str " was generated differently ahead of the header and in it.");
    field
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the method " ++ GlobRef.print func_ref
          ++ str " was not generated ahead of the files.")

(** The methods made of [candidates] in the inductive [name], as its struct
    declares them ({!Borrow_projection.lend}), with their control lowered
    from their ControlIR where that is the bridge's to lower
    ({!Control_to_cpp_ir.lower_struct_methods}).  The struct is merged into
    its module's where it is the one the module is promoting, or [merged]
    says so. *)
let gen_methods ?(merged = false) name vars candidates =
  let merged =
    merged || Option.cata (fun r -> globref_equal r name) false !Cpp_state.eponymous_promote_ref
  in
  Control_to_cpp_ir.lower_struct_methods ~merged name vars
    (List.concat_map
       (fun c ->
         List.map Legacy_minicpp_to_cpp_ir.lower_member
           (Borrow_projection.lend ~coinductive:(Table.is_coinductive name) (gen_single_method name vars c)) )
       candidates )

(** Does the ML type [ml_ty] contain [ind_ref] (or a mutual sibling) anywhere
    in its type arguments, but NOT at the top level?  Used to detect fields
    like [list(tree(A))] inside [tree]'s definition, which need field-level
    [shared_ptr] wrapping instead of type-argument wrapping. *)
let ml_type_has_nested_self_ref ~ind_ref ml_ty =
  let ind_kn_opt =
    match ind_ref with
    | GlobRef.IndRef (kn, _) -> Some kn
    | _ -> None
  in
  let is_self_or_mutual r =
    globref_equal r ind_ref
    || match r, ind_kn_opt with
       | GlobRef.IndRef (kn2, _), Some kn ->
         MutInd.CanOrd.equal kn2 kn
       | _ -> false
  in
  let rec has_self_ref = function
    | Miniml.Tglob (r, args, _) ->
      is_self_or_mutual r || List.exists has_self_ref args
    | Miniml.Tmeta {contents = Some t} -> has_self_ref t
    | Miniml.Tarr (t1, t2) ->
      has_self_ref t1 || has_self_ref t2
    | _ -> false
  in
  match ml_ty with
  | Miniml.Tglob (r, args, _) when not (is_self_or_mutual r) ->
    List.exists has_self_ref args
  | Miniml.Tmeta {contents = Some (Miniml.Tglob (r, args, _))}
    when not (is_self_or_mutual r) ->
    List.exists has_self_ref args
  | _ -> false

(** Does [ml_ty] recurse into [ind_ref] specifically THROUGH a boxed-element
    container (a container carrying a [Boxed Element] wrapper, e.g. [list <self>]
    mapped to [immer::flex_vector<immer::box<self>>])?  When it does, the element
    box already breaks the completeness cycle, so the outer field-level
    [shared_ptr]/arena-pointer indirection is redundant and the field can be
    stored by value. *)
let ml_type_recurses_through_boxed_container ~ind_ref ml_ty =
  let rec find_boxed_rec t =
    match t with
    | Miniml.Tglob (g, args, _) ->
      ( match Table.find_boxed_wrapper_opt g with
      | Some _ when ml_type_has_nested_self_ref ~ind_ref t -> true
      | _ -> List.exists find_boxed_rec args )
    | Miniml.Tarr (a, b) -> find_boxed_rec a || find_boxed_rec b
    | Miniml.Tmeta {contents = Some t'} -> find_boxed_rec t'
    | _ -> false
  in
  find_boxed_rec ml_ty

(** Completeness-aware element wrapping: if a constructor field of [ind_ref]
    recurses THROUGH a boxed-element container (a container carrying a
    [Boxed Element] wrapper, e.g. [list <self>] where
    [list -> immer::flex_vector]), record [ind_ref] as an inductive that must
    be boxed as a container element everywhere it occurs, so its C++
    representation is type-consistent: a type is complete only after its
    definition, and a container of the incomplete type is legal only when
    each element sits behind a box.  Call this for every constructor field
    type. *)
let maybe_record_boxed_recursive_ind ~ind_ref ml_ty =
  if ml_type_recurses_through_boxed_container ~ind_ref ml_ty then
    Table.add_boxed_recursive_ind ind_ref

(** The type a constructor struct of the inductive [name] stores field [ty]
    at, under the variable names [var_names]: recursive occurrences and,
    under [Crane BoxedFields], held inductives behind the smart pointer.
    Every reading of a field's storage -- the struct, its factories, its
    conversion to another instantiation, the pointer fields planned before
    rendering -- comes from here.  Recursive fields are always the ordinary
    smart pointer ([Tshared_ptr], rendered as std::shared_ptr / crane::rc);
    whether an object lives in an arena is decided per object at the factory
    call site, not baked into the field type. *)
let constructor_field_storage ~name ~is_coinductive var_names ty =
  let cpp_ty =
    convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Ref.User.Set.singleton name) var_names ty
  in
  (* Wrap fields that contain a nested self-reference in
     their type arguments (e.g. list(tree(A)) inside tree).
     The cycle is broken at the field level using a bare
     (no-ns) type so the outer shared_ptr provides pointer
     indirection without extra inner shared_ptrs for elements.
     E.g. option(chain) → shared_ptr<optional<chain>>,
          list(tree)   → shared_ptr<List<tree>>.
     The body sees *a0 at the bare type directly with no
     element-wise conversion needed. *)
  (* Completeness-aware element wrapping: record [name] as boxed wherever it
     is a container element ({!maybe_record_boxed_recursive_ind}). *)
  maybe_record_boxed_recursive_ind ~ind_ref:name ty;
  let bare_cpp_ty = convert_ml_type_to_cpp_type (empty_env ()) var_names ty in
  if ml_type_has_nested_self_ref ~ind_ref:name ty && not is_coinductive then
    (* If the field recurses THROUGH a boxed-element container, the
       element box already breaks the completeness cycle, so the outer
       shared_ptr/arena pointer is redundant: store the container by
       value. *)
    if ml_type_recurses_through_boxed_container ~ind_ref:name ty then bare_cpp_ty
    else Tshared_ptr bare_cpp_ty
  else
    match cpp_ty with
    | Tshared_ptr _ -> cpp_ty
    | _ when (not is_coinductive) && boxes_field ty -> Tshared_ptr bare_cpp_ty
    | _ when (not is_coinductive) && boxes_param_field ~owner:name ty && bare_cpp_ty <> Tany ->
      Tid_external (Crane_rt.field, [bare_cpp_ty])
    | _ -> cpp_ty

(** A field's storage type at the inductive's own variables [vars], erased
    where the inductive has none. *)
let constructor_field_at_own_vars vars cpp_ty =
  if vars = [] then
    match cpp_ty with
    | Tshared_ptr _ -> tvar_erase_type cpp_ty
    | _ when has_unnamed_tvar cpp_ty -> Tany
    | _ -> cpp_ty
  else cpp_ty

(** The fields of a constructor of [name], of types [tys], that its struct
    stores behind the smart pointer, each with whether it holds [name]
    itself: what loop lowering reads off the struct, decided before it is
    generated ({!Loopify_analysis.install_ctor_ptr_fields}). *)
let constructor_pointer_fields ~name ~is_coinductive vars tys =
  List.concat
    (List.mapi
       (fun i ty ->
         match
           constructor_field_at_own_vars vars
             (constructor_field_storage ~name ~is_coinductive vars ty)
         with
         | Tshared_ptr (Tglob (r, _, _)) when globref_equal r name -> [(i, true)]
         | Tshared_ptr _ -> [(i, false)]
         | _ -> [] )
       tys )

(** Whether ML type [t] is a reference to [ref_name] applied to the same type
    variables [ref_vars], its parameters (i.e., a direct recursive or mutual
    recursive occurrence).  The arguments after them are a family's type
    indices, which its C++ type does not take: [succE : expr nat -> expr nat]
    holds an [expr] like any other. *)
let rec is_ref_to ref_name ref_vars = function
  | Miniml.Tglob (r, args, _) ->
    globref_equal r ref_name
    && List.length args >= List.length ref_vars
    && List.for_all
         (fun (j, arg) ->
           match arg with
           | Miniml.Tvar (_, k) -> k = j + 1
           | Miniml.Tmeta {contents = Some (Miniml.Tvar (Schematic, k))}
           | Miniml.Tmeta {contents = Some (Miniml.Tvar (Rigid, k))} ->
             k = j + 1
           | _ -> false)
         (List.mapi (fun j a -> (j, a)) (CList.firstn (List.length ref_vars) args))
  | Miniml.Tmeta {contents = Some t} -> is_ref_to ref_name ref_vars t
  | _ -> false

(* Short names for the CppIR modules the struct is built from. *)
module T = Cpp_ir.Type
module E = Cpp_ir.Expr
module S = Cpp_ir.Stmt
module F = Cpp_ir.Field
module B = Cpp_ir.Build
module V = F.Visibility
module Sec = F.Section

(* A translation result, converted where the struct takes it. *)
let lower_type = Legacy_minicpp_to_cpp_ir.lower_type
let lower_expr = Legacy_minicpp_to_cpp_ir.lower_expr

(** A plain static member function: no template parameters, no [this], and
    none of the qualifiers a real method carries.  Factories are the only
    producer -- they are methods with every flag off, so they are spelled as
    methods rather than as a second, near-identical field kind. *)
let static_method ~name ~ret ~params ~body : Cpp_ir.Lowered.phase F.Method.t =
  { name;
    globref = None;
    type_params = [];
    return_type = ret;
    params;
    body;
    receiver = Static;
    is_inline = false;
    no_pure = false;
    constexpr = Undecided;
    is_noexcept = false;
    is_conversion = false;
    binders = [];
    receiver_binder = None;
    loop = None }

(** [accessor ~no_pure name ret body] is the member [name] of the struct
    returning [ret] by [body], called on [this] and taking nothing else:
    [const] unless [is_const] says otherwise, an accessor's section unless
    [section] says otherwise. *)
let accessor ?(is_const = true) ?(is_inline = false) ?(section = F.Section.Accessors) ~no_pure name ret body
    : Cpp_ir.Lowered.phase F.member =
  ( Method
      { name = Id.of_string name;
        globref = None;
        type_params = [];
        return_type = ret;
        params = [];
        body;
        receiver = Instance {this_position = 0; is_const; ref_qualifier = Any; returns_field = false};
        is_inline;
        no_pure;
        constexpr = Undecided;
        is_noexcept = false;
        is_conversion = false;
        binders = [];
        receiver_binder = None;
        loop = None },
    Public,
    section )

(** [constructor ?tparams ?explicit params inits] is a constructor of the
    struct with an empty body, [explicit] unless said otherwise, in the
    creators' section. *)
let constructor ?(tparams = []) ?(explicit = true) params inits : Cpp_ir.Lowered.phase F.member =
  (Constructor {type_params = tparams; params; inits; body = []; explicit; noexcept = false}, Public, Creators)

(** {!Translation_support.qualify_inductives} in CppIR: each inductive [t]
    names wrapped in its namespace, those [skip] answers for and inline
    mappings excepted. *)
let rec qualify_inductives_lowered ~skip (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  let go = qualify_inductives_lowered ~skip in
  match t with
  | Entity_application (g, ts, es) -> (
    let core : Cpp_ir.Lowered.Type.t = Entity_application (g, List.map go ts, es) in
    match g with
    | GlobRef.IndRef _ when skip g -> core
    | GlobRef.IndRef _ when Table.is_inline_custom g -> core
    | GlobRef.IndRef _ -> In_namespace (g, core)
    | _ -> core )
  | In_namespace (g, t) -> (
    let inner = go t in
    match inner with In_namespace (g2, _) when GlobRef.CanOrd.equal g g2 -> inner | _ -> In_namespace (g, inner) )
  | Shared_pointer t -> Shared_pointer (go t)
  | Reference (k, t) -> Reference (k, go t)
  | Const t -> Const (go t)
  | Pointer t -> Pointer (go t)
  | Function (args, ret) -> Function (List.map go args, go ret)
  | Named (id, ts) -> Named (id, List.map go ts)
  | External (id, ts) -> External (id, List.map go ts)
  | Non_deduced t -> Non_deduced (go t)
  | Rebind (h, x) -> Rebind (go h, go x)
  | Member (base, id) -> Member (go base, id)
  | t -> t

(** {!Minicpp.mk_lambda} in CppIR, for a lambda with no template parameters
    of its own: a [const] on the return type is dropped, and a nullary
    lambda whose body only throws is that abort. *)
let lambda params ret body ~(capture : Cpp_ir.Lowered.phase E.Capture.t) : Cpp_ir.Lowered.Expr.t =
  let return_type = match ret with Some (T.Const t) -> Some t | r -> r in
  match (params, body) with
  | [], [S.Throw msg] -> E.Abort (msg, match return_type with Some t -> t | None -> T.Any)
  | _ -> E.Lambda {params; type_params = []; return_type; body; capture; moved = []; binders = []; fixpoint = None}

(** Generate the C++ declaration of an inductive type: an encapsulated struct
    with its methods.

    Produces one of four shapes depending on the inductive:
    {ul
    {- {b Empty}: a struct whose default constructor is deleted.}
    {- {b Enum}: a plain [enum class], for a non-mutual, non-custom inductive
       without parameters whose constructors are all nullary.}
    {- {b Flat}: a plain struct of public fields, for a flat inductive
       ({!Table.is_flat_inductive}), with [clone], a conversion to another
       instantiation and one factory.}
    {- {b Variant}: a struct with a nested struct per constructor
       alternative (e.g. [Leaf {}], [Node { ... }]), [using variant_t =
       std::variant<Leaf, Node>] and a private member of that type ([v_], or
       [d_v_] under BDE); a coinductive holds a [crane::lazy<variant_t>]
       ([lazy_v_] / [d_lazyV_]) instead.}}

    The variant shape's members, in order: constructor structs, the variant
    alias, the marker aliases [crane_family_tag] / [crane_cheap_copy] where
    they apply, the private member, a default constructor, an explicit
    constructor per alternative, the converting constructor from another
    instantiation, the coinductive's thunk constructor, static factory
    methods (with their [__reuse] variants under [Crane Reuse]), the
    coinductive's [lazy_] factory, the iterative destructor for recursive
    types with re-defaulted copy/move members, [v_mut()], mutating methods,
    [v()], the coinductive's [lazy_cell()], and const methods.  Every shape
    gets the methods from [method_candidates] ({!gen_methods}).

    @param is_mutual       whether this type is part of a mutual block
    @param consarg_names   binder names from
                           {!Miniml.ml_ind_packet.ip_consarg_names}, indexed by
                           constructor: struct fields and factory parameters
                           use them instead of positional names ([d_a0])
    @param mutual_partners the other types of the mutual block, each with its
                           constructors, their argument types and binder
                           names
    @param vars            the inductive's template variable names
    @param name            the inductive
    @param cnames          its constructors
    @param tys             the argument types of each constructor
    @param method_candidates
      functions to generate as methods: [(func_ref, body, type, this_pos)]
    @param ind_kind        whether the inductive is coinductive *)
let gen_ind_header_v2
    ?(is_mutual = false)
    ?(consarg_names = [||])
    ?(mutual_partners = [])
    vars
    name
    cnames
    tys
    method_candidates
    ind_kind =
  let is_coinductive = ind_kind = Core.Inductive.Kind.Coinductive in
  (* Arena allocation is not a compile-time property of the type.  Every
     recursive field is the ordinary smart pointer ([std::shared_ptr] /
     [crane::rc]); the recursive-field factory
     is the *runtime-arena-aware* one ([crane::arena_make_shared] /
     [crane::rc<T>::make], see [Arena_scoped]), which bump-allocates from the
     current arena only when a [crane::arena_scope] is open at the call site and
     otherwise falls back to a plain heap allocation.  [arena_runtime_ok] just
     decides whether the generated factory contains that runtime branch at all:
     it requires the [Set Crane Arena] master switch (off by default, so the
     common case emits the plain make_shared/make_rc factory and pulls in no
     arena runtime); it is further suppressed for [Crane NoArena] types (which
     must never bump-allocate), and for coinductive (lazy thunks) and mutually
     recursive ([std::any]) types whose special field handling the runtime-arena
     path does not cover -- those keep the plain make_shared factory too. *)
  let arena_runtime_ok =
    Table.arena_enabled ()
    && Table.should_use_arena_at_runtime name
    && (not is_coinductive)
    && not is_mutual
  in
  let templates =
    hkt_templates name vars (List.concat (Array.to_list tys))
  in
  let type_params = templates in
  let ty_vars = List.map B.named_variable vars in

  (* Handle empty inductives (no constructors) - generate uninhabitable
     struct *)
  if Array.length cnames = 0 then
    (* For empty types like `Inductive empty : Type := .`, generate: struct
       empty { empty() = delete; }; This type cannot be constructed, matching
       the semantics of empty types. *)
    let method_fields =
      gen_methods name vars method_candidates
    in
    (Struct
       { ref_ = name;
         fields = [(F.Deleted_default_constructor, V.Public, Sec.Untagged)] @ method_fields;
         type_params;
         constraint_ = None;
         needs_shared_from_this = false }
      : Cpp_ir.Lowered.Decl.t)
  else (* Check if all constructors are nullary: eligible for enum class *)
    let all_nullary = Array.for_all (fun tys_list -> tys_list = []) tys in
    if all_nullary && vars = [] && (not is_mutual) && not (is_custom name) then (
      (* Register as enum inductive for type/constructor/match generation *)
      Table.add_enum_inductive name;
      let ctor_names =
        Array.to_list
          (Array.map
             (fun c ->
               match c with
               | GlobRef.ConstructRef ((kn, i), cidx) ->
                 Id.of_string (Common.enum_ctor_name_of_ref kn i cidx)
               | _ -> ctor_fallback_id 0 )
             cnames )
      in
      let rocq_names =
        Array.to_list
          (Array.map
             (fun c ->
               match c with
               | GlobRef.ConstructRef _ -> Common.pp_global_name Type c
               | _ -> "" )
             cnames )
      in
      (Enum {ref_ = name; ctors = ctor_names; rocq_names; type_params = []} : Cpp_ir.Lowered.Decl.t) )
    else
      (* The main struct type: all inductives (including coinductives)
         are value types. *)
      let self_ty = T.Entity_application (name, ty_vars, []) in

      (* Preparation registered the flat inductives
         ({!Table.is_flat_inductive_packet}). *)
      if Table.is_flat_inductive name then begin
        let tys_list = tys.(0) in
        let c = cnames.(0) in
        let cname_str = ctor_struct_name_of_ref ~fallback_idx:0 c in
        let ctor_consarg_names =
          if 0 < Array.length consarg_names then consarg_names.(0) else [] in
        let n_fields = List.length tys_list in
        let field_ids =
          compute_and_register_field_names ~owner:c cname_str
            (augment_with_args_renaming c ctor_consarg_names)
            ctor_consarg_names n_fields in
        let erase_if_needed cpp_ty =
          if vars = [] then
            match cpp_ty with
            | Tshared_ptr _ -> tvar_erase_type cpp_ty
            | _ when has_unnamed_tvar cpp_ty -> Tany
            | _ -> cpp_ty
          else cpp_ty
        in
        (* A field's value type, and the type the struct stores it at:
           boxed under [Crane BoxedFields] when it holds an inductive. *)
        let value_ty var_names ty =
          erase_if_needed (convert_ml_type_to_cpp_type (empty_env ()) var_names ty)
        in
        let stored_ty var_names ty =
          let t = value_ty var_names ty in
          if boxes_field ty then Tshared_ptr t else t
        in
        let flat_fields =
          List.mapi (fun j ty ->
            ((F.Data (List.nth field_ids j, lower_type (stored_ty vars ty)), V.Public, Sec.Data) : Cpp_ir.Lowered.phase F.member)
          ) tys_list
        in
        let field_exprs = List.map (fun fid -> E.Local fid) field_ids in
        let clone_body = [S.Return (Some (E.Braced field_exprs))] in
        let clone_field = accessor ~no_pure:true "clone" self_ty clone_body in
        let conversion_field =
          (* An inductive's [vars] already begin with its promoted variables
             (see [Cpp_ind]), so nothing is left to keep. *)
          conversion_to_other_instantiation ~leading:[] ~name ~templates ~vars
            ~fields:
              (List.mapi
                 (fun j ty -> (List.nth field_ids j, fun var_names -> stored_ty var_names ty))
                 tys_list)
        in
        let factory_name = Id.of_string (factory_name_of_ctor c) in
        let factory_params =
          List.mapi (fun j ty -> (List.nth field_ids j, value_ty vars ty)) tys_list
        in
        let factory_args =
          List.map2 (fun (param_name, cpp_ty) ty : Cpp_ir.Lowered.Expr.t ->
            if boxes_field ty then
              B.call (E.Allocate (Heap, lower_type cpp_ty)) [E.Move (E.Local param_name)]
            else if is_trivially_copyable_type cpp_ty then E.Local param_name
            else E.Move (E.Local param_name)
          ) factory_params tys_list
        in
        let factory_body = [S.Return (Some (E.Braced factory_args))] in
        let factory_field : Cpp_ir.Lowered.phase F.member =
          ( Method
              (static_method ~name:factory_name ~ret:self_ty
                 ~params:(List.map (fun (x, t) -> (x, lower_type t)) factory_params) ~body:factory_body),
            V.Public, Sec.Creators )
        in
        let method_fields = gen_methods name vars method_candidates in
        let all_flat_fields =
          flat_fields @ [clone_field] @ conversion_field @ [factory_field]
          @ method_fields
        in
        (Struct
           { ref_ = name;
             fields = all_flat_fields;
             type_params;
             constraint_ = None;
             needs_shared_from_this = false }
          : Cpp_ir.Lowered.Decl.t)
      end else



      let field_storage_ty var_names ty = constructor_field_storage ~name ~is_coinductive var_names ty in
      let compute_field_cpp_ty ty =
        let cpp_ty = field_storage_ty vars ty in
        constructor_field_at_own_vars vars cpp_ty
      in
      (* A coinductive's constructor struct holds values of the coinductive
         itself and of its mutual siblings, each incomplete inside its own
         body.  Each of those types becomes a parameter of the struct, so the
         struct is completed only once they are. *)
      let deferred_ctor_struct cname fields =
        let group =
          (* Mutual siblings share their parameters. *)
          (name, vars)
          :: List.map (fun (pname, _, _, _) -> (pname, vars)) mutual_partners
        in
        let selves =
          List.mapi
            (fun k (r, rvars) ->
              ( (r, List.length rvars),
                ( Generated_name.indexed "S" k,
                  Tglob (r, List.map named_tvar rvars, []) ) ) )
            group
        in
        let through_selves =
          map_cpp_type (fun t ->
            match t with
            | Tglob (r, args, _) | Tnamespace (_, Tglob (r, args, _)) -> (
              match
                List.find_opt
                  (fun ((r', n), _) -> globref_equal r r' && List.length args = n)
                  selves
              with
              | Some (_, (id, _)) -> named_tvar id
              | None -> t )
            | _ -> t )
        in
        (List.map snd selves, List.map (fun (f, ty) -> (f, through_selves ty)) fields)
      in
      (* 1. Constructor alternative structs (simple, just fields, no make) *)
      let constructor_structs =
        Array.to_list
          (Array.mapi
             (fun i tys_list ->
               let c = cnames.(i) in
               let cname = ctor_struct_id_of_ref ~fallback_idx:i c in
               (* Fields: convert types, using self_ty for recursive
                  references *)
               let ctor_struct_name = Id.to_string cname in
               let ctor_consarg_names =
                 if i < Array.length consarg_names then consarg_names.(i)
                 else []
               in
               let n_fields = List.length tys_list in
               let field_ids =
                 compute_and_register_field_names ~owner:c ctor_struct_name
                   (augment_with_args_renaming c ctor_consarg_names)
                   ctor_consarg_names n_fields
               in
               let fields =
                 List.mapi
                   (fun j ty -> (List.nth field_ids j, compute_field_cpp_ty ty))
                   tys_list
               in
               (* Deferred only where a field names the incomplete type. *)
               let lower_fields = List.map (fun (f, ty) -> (f, lower_type ty)) in
               let selves, deferred_fields = deferred_ctor_struct cname fields in
               if is_coinductive && deferred_fields <> fields then
                 ( (F.Deferred_struct {name = cname; selves = lower_fields selves; fields = lower_fields deferred_fields}
                     : Cpp_ir.Lowered.phase F.t),
                   V.Public,
                   Sec.Types )
               else
                 ( F.Nested_struct
                     ( cname,
                       List.map
                         (fun (f, ty) : Cpp_ir.Lowered.phase F.member -> (F.Data (f, lower_type ty), V.Public, Sec.Untagged))
                         fields ),
                   V.Public,
                   Sec.Types ) )
             tys )
      in

      (* 2. variant_t type alias - use simple Id-based refs that match nested struct names *)
      (* Note: nested structs inherit template params from parent, so don't add <A> to them *)
      let variant_ty : Cpp_ir.Lowered.Type.t =
        T.Variant
          ( (if Table.is_shared_variant name then Shared else Inline),
            Array.to_list
             (Array.mapi
                (fun i c ->
                  let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                  (* Use T.Named for local nested struct types - no template args
                     since they inherit *)
                  T.Named (cname_id, []) )
                cnames ) )
      in
      (* Collision detection: internal names must not equal the enclosing type name *)
      let type_name_str = Common.pp_global_name Type name in
      let escape_if_clashes base =
        if String.equal base type_name_str then base ^ "_" else base
      in
      let variant_alias_name = escape_if_clashes "variant_t" in
      let variant_using : Cpp_ir.Lowered.phase F.member =
        (F.Nested_type_alias ([], Id.of_string variant_alias_name, variant_ty), V.Public, Sec.Types)
      in
      (* A type parameterised by families is itself one: [crane::rebind_t]
         leaves it alone, as the family's own struct it is, rather than
         reading its erased index as an element (see [obj.h]). *)
      let element_using : Cpp_ir.Lowered.phase F.member list =
        if List.exists (fun i -> Table.is_family_ind_param name i)
             (List.init (List.length vars) Fun.id)
        then
          [ ( F.Nested_type_alias ([], Id.of_string "crane_family_tag", T.Void),
              V.Public,
              Sec.Types ) ]
        else []
      in
      (* A coinductive value is a lazy cell, as cheap to copy as a pointer:
         a [crane::field] of it is not boxed (see field.h). *)
      let element_using =
        if is_coinductive && Table.boxed_fields () then
          element_using
          @ [(F.Nested_type_alias ([], Id.of_string "crane_cheap_copy", T.Void), V.Public, Sec.Types)]
        else element_using
      in

      (* 3. Private variant member: v_ for inductive, lazy_v_ for coinductive *)
      let variant_member_name =
        escape_if_clashes
          (if Table.std_lib () = "BDE" then
             (if is_coinductive then "d_lazyV_" else "d_v_")
           else
             (if is_coinductive then "lazy_v_" else "v_"))
      in
      let variant_alias_id = Id.of_string variant_alias_name in
      let variant_alias_ty : Cpp_ir.Lowered.Type.t = T.Named (variant_alias_id, []) in
      let vmn_id = Id.of_string variant_member_name in
      let variant_member_ty =
        if is_coinductive then
          T.External (Crane_rt.lazy_, [variant_alias_ty])
        else
          variant_alias_ty
      in
      let variant_member : Cpp_ir.Lowered.phase F.member =
        ( F.Data (Id.of_string variant_member_name, variant_member_ty),
          V.Private,
          Sec.Data )
      in

      (* A coinductive's cell type, [crane::lazy<variant_t>], as the callee of
         its constructor. *)
      let lazy_cell : Cpp_ir.Lowered.Expr.t =
        E.Local (Id.of_string_soft (Crane_rt.lazy_ ^ "<" ^ variant_alias_name ^ ">"))

      in

      (* 4. Public explicit constructors for each alternative.
         Public so that std::make_shared can construct instances directly
         (single allocation). *)
      (* Note: nested struct types don't need template args - they inherit from parent *)
      let public_ctors =
        Array.to_list
          (Array.mapi
             (fun i c ->
               let cname = ctor_struct_id_of_ref ~fallback_idx:i c in
               let param_name = Id.of_string "_v" in
               let param_ty = T.Named (cname, []) in
               if is_coinductive then
                 (* For coinductive:
                    d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) *)
                 let init_expr =
                   B.call lazy_cell
                     [ B.call (E.Local variant_alias_id)
                         [E.Move (E.Local param_name)] ]
                 in
                 let init_list = [(vmn_id, init_expr)] in
                 constructor [(param_name, param_ty)] init_list
               else
                 (* For inductive: d_v_(std::move(_v)) when the constructor
                    struct has non-trivial fields (shared_ptr etc.).  For
                    trivially-copyable structs (e.g., empty nullary constructors
                    like O, Nil, Leaf), skip std::move: it has no effect and
                    triggers performance-move-const-arg. *)
                 let has_nontrivial_fields =
                   List.exists (fun ty -> not (isTdummy ty)) tys.(i)
                 in
                 let init_v =
                   if has_nontrivial_fields then E.Move (E.Local param_name)
                   else E.Local param_name
                 in
                 let init_list =
                   [(vmn_id, init_v)]
                 in
                 constructor [(param_name, param_ty)] init_list )
             cnames )
      in

      (* Default constructor, which lets loopify declare [T _result{};] for
         stack-based iteration.  An inductive's variant default-constructs to
         its first alternative (e.g. Nil); a coinductive's lazy cell to an
         empty one -- the state a moved-from value is already in, and which
         only a slot written before it is read, as [_result] is, may hold. *)
      let default_ctor =
        [constructor ~explicit:false [] []]
      in

      (* Iterative destructor preventing stack overflow from deeply recursive
         [shared_ptr] chains.  Drains recursive fields into an explicit stack,
         only entering nodes with [use_count() == 1] (sole ownership).

         Self-recursive types use [shared_ptr<Self>] directly on the stack.
         Mutually recursive types use [std::any] to hold different [shared_ptr]
         types.  Returns [[]] for non-recursive or coinductive types, and for
         a shared variant, whose blocks the runtime already frees iteratively
         (shared_block.h's [free_block]). *)
      let iterative_destructor =
        (* Recursive fields are ordinary smart pointers even for arena-backed
           values (the region only owns the payload memory; per-node
           refcounting still drives destruction), so the
           iterative destructor that drains those smart-pointer chains is
           needed here exactly as for any other recursive type. *)
        if is_coinductive || Table.is_shared_variant name then []
        else
          let is_direct_self_ref t = is_ref_to name vars t in
          (* Does [t] mention the inductive being generated anywhere, at any
             depth?  [is_direct_self_ref] only matches the type at the root. *)
          let rec contains_self t =
            is_direct_self_ref t
            || match t with
               | Miniml.Tmeta {contents = Some t'} -> contains_self t'
               | Miniml.Tglob (_, args, _) -> List.exists contains_self args
               | Miniml.Tarr (a, b) -> contains_self a || contains_self b
               | _ -> false
          in
          let is_mutual_ref ty =
            List.exists
              (fun (pname, _, _, _) -> is_ref_to pname vars ty)
              mutual_partners
          in
          (* Self-recursion routed through another user-defined inductive
             (e.g. [RNode : box rose -> rose], where [box] is a plain
             one-field wrapper).  The occurrence is neither direct nor a
             list, so without this the type would look non-recursive, no
             drain would be emitted at all, and destruction would recurse once
             per level
             through the default member-wise [~shared_ptr] chain -- a stack
             overflow on deep values (CWE-674; regression:
             tests/regression/wrapper_nested_recursion_no_drain).

             Restricted to "flat" wrappers: single-constructor inductives
             laid out as a plain struct, so a uniquely-owned
             [shared_ptr<box<rose>>] reaches its nested [rose] by a direct
             member access.  Multi-constructor wrappers would need per-
             alternative [get_if] dispatch and are still classified [`None].

             Returns the wrapper's field names that hold a self-reference:
             those whose declared type is a parameter the field instantiates
             with [Self], plus any that name [Self] outright. *)
          let wrapper_self_fields g args =
            match g with
            | GlobRef.IndRef (kn, i) when Table.is_flat_inductive g ->
              let ctor = GlobRef.ConstructRef ((kn, i), 1) in
              (match Table.get_ctor_ip_types_opt ctor with
               | None -> []
               | Some ip_types ->
                 let cname_str = ctor_struct_name_of_ref ~fallback_idx:0 ctor in
                 let nargs = List.length args in
                 List.filter_map
                   (fun (j, fty) ->
                     let rec holds_self = function
                       | Miniml.Tvar (_, k) ->
                         k >= 1 && k <= nargs
                         && is_direct_self_ref (List.nth args (k - 1))
                       | Miniml.Tmeta {contents = Some t} -> holds_self t
                       | t -> is_direct_self_ref t
                     in
                     if holds_self fty
                     then Some (Common.lookup_ctor_field_name ~owner:ctor cname_str j)
                     else None)
                   (List.mapi (fun j t -> (j, t)) ip_types))
            | _ -> []
          in
          (* Recognise a "list-shaped" inductive: exactly two constructors, the
             first nullary and the second [A -> g A -> g A].  That is the shape
             the [`List] drain below knows how to walk iteratively.

             [is_list_global] matches only the stdlib [list], by identity.  A
             user-defined inductive of the same shape needs the same treatment,
             because a type whose recursion goes *through* it --
             [Inductive tree := node : nat -> lst tree -> tree] -- has no direct
             self-reference and so would otherwise get no iterative drain at
             all.  Destroying a deep value then recurses
             ~lst<tree> -> ~tree -> ~lst<tree> -> ... and overflows the stack. *)
          let is_list_shaped_ind g =
            match g with
            | GlobRef.IndRef (kn, i) ->
              let ctor j =
                Table.get_ctor_ip_types_opt (GlobRef.ConstructRef ((kn, i), j))
              in
              (* A third constructor means this is not the Nil/Cons shape. *)
              ctor 3 = None
              && (match (ctor 1, ctor 2) with
                  | Some [], Some [elem; tail] ->
                    let is_first_tvar t =
                      match Ml_type_util.resolve_tmeta t with
                      | Miniml.Tvar (_, 1) -> true
                      | _ -> false
                    in
                    let is_self t =
                      match Ml_type_util.resolve_tmeta t with
                      | Miniml.Tglob (g', _, _) -> globref_equal g' g
                      | _ -> false
                    in
                    is_first_tvar elem && is_self tail
                  | _ -> false)
            | _ -> false
          in
          let rec classify_ml_self_ref = function
            | ml_ty when is_direct_self_ref ml_ty -> `Direct
            | Miniml.Tglob (g, [arg], _)
              when (is_list_global g || is_list_shaped_ind g)
                   && is_direct_self_ref arg ->
              `List g
            | Miniml.Tmeta {contents = Some t} -> classify_ml_self_ref t
            | Miniml.Tglob (g, args, _) as ml_ty
              when not (globref_equal g name) ->
              (match wrapper_self_fields g args with
               | [] ->
                 (* Recursion routed through some *other* mediating shape --
                    [prod], [option], a record, a list of pairs, a nested list,
                    a user-defined option-like inductive, ...  The cases above
                    cover the direct, list-shaped and flat-wrapper shapes,
                    which have dedicated drains; everything else is handed to
                    [harvest_field],
                    which walks the mediator's structure and moves out every
                    [Self] it reaches.  See its comment for the traversal. *)
                 if List.exists contains_self args then `Nested ml_ty else `None
               | fields -> `Wrapper fields)
            | _ -> `None
          in
          let has_mutual =
            Array.exists (fun tys_list ->
              List.exists is_mutual_ref tys_list) tys
          in
          (* Shared identifiers used across the destructor body *)
          let _stack_id = Id.of_string "_stack" in
          let _alt_id = Id.of_string "_alt" in
          let _v_id = Id.of_string "_v" in
          let _cur_id = Id.of_string "_cur" in
          let _sp_id = Id.of_string "_sp" in
          let _pv_id = Id.of_string "_pv" in
          (* The alias, under whatever name it was actually emitted: an
             inductive named [variant_t] pushes it to [variant_t_]. *)
          let variant_t_ty = variant_alias_ty in
          let self_ty : Cpp_ir.Lowered.Type.t = T.Entity_application (name, ty_vars, []) in
          (* Qualify inductive references for use outside [name]'s own scope;
             [name] itself is skipped because the destructor is written inside
             it. *)
          let q_destr ty =
            let skip g = GlobRef.CanOrd.equal g name in
            qualify_inductives_lowered ~skip ty
          in
          (* Expand a [Drain "..."] template for a custom container field into a
             statement list. [%scrut] -> the container field expression [scrut];
             [%yield(e)] -> a structured [push_back(make_rc<Self>(e))] onto the
             worklist. The template is split into raw chunks around the structured
             pushes so that the [_stack] reference is a real [E.Local] the lambda
             capture-analysis can see (a fully-raw body would collapse to an
             empty [[]] capture). [%yield]'s argument is captured with
             balanced-paren matching, so it may itself contain parentheses
             (e.g. [std::move(%scrut.front())]). *)
          let expand_drain_template ~scrut ~self tmpl =
            let subst s = Common.render_template [("%scrut", scrut)] s in
            List.map
              (function
                | Foreign_template.Drain_text t -> S.Foreign_text (subst t)
                | Drain_yield arg ->
                  S.Expression
                    (E.Access_call
                       ( Dot,
                         E.Local _stack_id,
                         Id.of_string "push_back",
                         [B.call (E.Allocate (Heap, self)) [E.Foreign_text (subst arg)]] )) )
              (Foreign_template.drain_template tmpl)
          in
          (* Every drain below establishes sole ownership with
             [p && p.use_count() == 1] and then mutates the pointee, moving a
             value out of it.  Emitted right after each such test, before the
             first access to the pointee.  Why that is thread-safe:

             1. The count cannot rise behind our back, so this is not a
                check-then-use race.  Incrementing a refcount requires copying
                an existing owning pointer, i.e. already holding a reference.
                If the count is 1 and *we* hold that one reference, no other
                owning pointer exists anywhere, so there is nothing for another
                thread to copy from.  The only ways to obtain a reference from
                a non-owning handle -- weak_ptr::lock, shared_from_this -- both
                require an existing strong reference to succeed.  So once we
                observe 1 from the sole-owner position, the value is stable.

                The error is one-sided, in the safe direction: a spuriously
                *high* reading is possible (another owner's decrement not yet
                visible to us) and merely stops the drain early, leaving the
                node to die with its real owner.  A spuriously *low* reading,
                the dangerous one, cannot occur.

             2. What the bare count test does not give us, against an atomic
                control block, is *synchronization*.  [use_count] is a relaxed
                load, so on its own it establishes no happens-before with the
                release-decrement of the owner that just dropped the other
                reference: our writes into the node could formally race with
                that owner's last reads of it.  The fence supplies the missing
                acquire edge.

             The fence must come *after* the load, not before.  Per
             [atomics.fences]p4, a release operation A synchronizes with an
             acquire fence B only if some atomic operation X reads the value
             written by A and X is *sequenced before* B.  Here A is the other
             thread's release-decrement, X is our [use_count] load, and B is
             this fence -- so X has to precede B.  A fence hoisted above the
             load has no such X and is a no-op for this purpose.  The fence is
             retroactive: the load carries the value, and the fence upgrades it
             to an acquire.  (Rule of thumb: acquire fence after the load,
             release fence before the store.)  This mirrors shared_ptr's own
             destructor, which acquire-fences after observing the last
             reference and before running the deleter.

             With three or more owners we synchronize with every dropper, not
             just the last: refcount decrements are read-modify-writes and so
             form a release sequence, and reading its final value picks up the
             whole chain.  That is the same argument that makes refcounting
             work at all.

             Under [Crane NonAtomicRc] the control block is single-threaded --
             no atomics, no decrement to pair with -- so no fence is emitted,
             and <atomic>, which {!Cpp_demands} demands for the fence's text,
             is not included on its account. *)
          let unique_fence =
            if Table.non_atomic_rc () then []
            else [S.Foreign_text Cpp_demands.acquire_fence]
          in
          let is_sole p =
            E.Binary (Equal, E.Access_call (Dot, p, Id.of_string "use_count", []), E.Literal (Int 1))
          in
          (* Generic mediator harvester.

             A constructor field whose type merely *contains* [Self] --
             [(Self * nat)], [option (option Self)], [list (nat * Self)],
             [cell Self], [w Self] where [w] holds a [list] -- reaches its
             nested [Self]s through an arbitrary composition of products,
             options, records and other inductives.  Giving each such shape
             its own case in [classify_ml_self_ref] would leave every
             unrecognised one with no drain at all, so destroying a deep value
             would recurse once per level and overflow the stack (CWE-674).

             Instead of enumerating shapes, [harvest_val] walks the mediator's
             *type* and emits the C++ that walks the corresponding value,
             moving every [Self] it finds onto the destructor's worklist.  Two
             mutually recursive halves:

             - [harvest_val ty e]: [e] is a bare lvalue of [ty]'s value type.
             - [harvest_ptr ty p]: [p] is a [shared_ptr] to one, so it first
               establishes sole ownership ([p && p.use_count() == 1], plus the
               acquire fence -- see [unique_fence]) and resets [p] afterwards.

             The representation rule the two rely on is the one
             [compute_field_cpp_ty] implements: a constructor field is behind a
             [shared_ptr] exactly when its declared type names its own
             inductive or nests a reference to it; type *arguments* are always
             stored bare.  [field_is_ptr] mirrors that decision.

             A mediator that recurses into itself (a list spine, a tree) cannot
             be expanded inline -- generation would not terminate -- so it gets
             its own local worklist and a loop, which is also what keeps the
             generated code's stack depth bounded.  Ownership is re-established
             per cell inside that loop, not just at the head: cells share their
             tails, so a suffix may still belong to a live value.

             Anything the walk does not understand (custom containers other
             than [std::pair]/[std::optional], mutual blocks, non-uniform
             recursion, or a type nested deeper than [harvest_fuel]) raises
             [Harvest_bail] and the field is left undrained -- the same as
             having no drain for it, never something worse. *)
          let harvest_fuel = 12 in
          let hv_seq = ref 0 in
          let fresh_hv p =
            incr hv_seq;
            p ^ string_of_int !hv_seq
          in
          let cpp_of_ml t =
            lower_type (convert_ml_type_to_cpp_type (empty_env ()) vars t)
          in

          (* Spelled as from outside the inductive's own scope, which is where
             the destructor's helper types are named. *)
          let outer_ty = q_destr in
          let outer_ml t = outer_ty (cpp_of_ml t) in
          (* [e.m()] -- the harvester only ever calls nullary members
             ([use_count], [reset], [has_value], [v_mut]) on a value. *)
          let dot0 e m = E.Access_call (Dot, e, Id.of_string m, []) in
          (* [p->m()], for a [p] that is a raw or smart pointer. *)
          let arrow0 e m = E.Access_call (Arrow, e, Id.of_string m, []) in
          (* Guard [body] on [p] being the sole owner of its pointee -- every
             drain moves a value out of one, so it must first establish that
             nobody else can see it.  The acquire fence follows the [use_count]
             test rather than preceding it; see [unique_fence]. *)
          let sole_owner p body =
            [S.If {condition = E.Binary (And, p,
                E.Binary (Equal, dot0 p "use_count", E.Literal (Int 1))); then_ = unique_fence @ body; else_ = []}]
          in
          (* [_stack.push_back(make_shared<Self>(std::move(e)))] -- hand one
             discovered [Self] to the destructor's worklist. *)
          let push_self_stmt e =
            S.Expression (E.Access_call (Dot, 
              E.Local _stack_id,
              Id.of_string "push_back",
              [ B.call
                  (E.Allocate (Heap, outer_ty self_ty))
                  [E.Move e] ]))
          in
          (* Substitute a mediator's actual type arguments into one of its
             declared constructor field types. *)
          let rec subst_targs args t =
            match t with
            | Miniml.Tmeta {contents = Some t'} -> subst_targs args t'
            | Miniml.Tvar (_, k) ->
              if k >= 1 && k <= List.length args then List.nth args (k - 1)
              else t
            | Miniml.Tglob (g, ts, l) ->
              Miniml.Tglob (g, List.map (subst_targs args) ts, l)
            | Miniml.Tarr (a, b) ->
              Miniml.Tarr (subst_targs args a, subst_targs args b)
            | _ -> t
          in
          (* [(ctor index (1-based), declared field types)] for every
             constructor of [g], or [None] if [g] is not an inductive we can
             enumerate. *)
          let ind_ctor_tys g =
            match g with
            | GlobRef.IndRef (kn, i) ->
              let rec go j acc =
                match
                  Table.get_ctor_ip_types_opt (GlobRef.ConstructRef ((kn, i), j))
                with
                | None -> List.rev acc
                | Some ftys -> go (j + 1) ((j, ftys) :: acc)
              in
              (match go 1 [] with [] -> None | l -> Some l)
            | _ -> None
          in
          let mentions g t =
            let rec go t =
              match t with
              | Miniml.Tmeta {contents = Some t'} -> go t'
              | Miniml.Tglob (g', args, _) ->
                globref_equal g' g || List.exists go args
              | Miniml.Tarr (a, b) -> go a || go b
              | _ -> false
            in
            go t
          in
          (* Mirrors [compute_field_cpp_ty]: is field type [fty] of inductive
             [g] stored behind a smart pointer? *)
          let field_is_ptr g fty =
            let root_is_g =
              match Ml_type_util.resolve_tmeta fty with
              | Miniml.Tglob (g', _, _) -> globref_equal g' g
              | _ -> false
            in
            (root_is_g || ml_type_has_nested_self_ref ~ind_ref:g fty)
            && not (ml_type_recurses_through_boxed_container ~ind_ref:g fty)
          in
          let exception Harvest_bail in
          let starts_with p s =
            String.length s >= String.length p
            && String.equal (String.sub s 0 (String.length p)) p
          in
          let rec harvest_val fuel ty e =
            if fuel <= 0 then raise Harvest_bail;
            let ty = Ml_type_util.resolve_tmeta ty in
            if is_direct_self_ref ty then [push_self_stmt e]
            else
              match ty with
              | Miniml.Tglob (g, args, _) when List.exists contains_self args ->
                (match Table.find_custom_opt g with
                 | Some tmpl when starts_with "std::optional" tmpl ->
                   (match args with
                    | [a] ->
                      let body = harvest_val (fuel - 1) a (E.Dereference e) in
                      if body = [] then []
                      else [S.If {condition = dot0 e "has_value"; then_ = body; else_ = []}]
                    | _ -> raise Harvest_bail)
                 | Some tmpl when starts_with "std::pair" tmpl ->
                   (match args with
                    | [a; b] ->
                      let fld n = E.Access (Dot, e, Id.of_string n) in
                      (if contains_self a
                       then harvest_val (fuel - 1) a (fld "first")
                       else [])
                      @ (if contains_self b
                         then harvest_val (fuel - 1) b (fld "second")
                         else [])
                    | _ -> raise Harvest_bail)
                 | Some _ -> raise Harvest_bail
                 | None -> harvest_ind (fuel - 1) g args e)
              | _ -> raise Harvest_bail
          and harvest_ptr fuel ty p =
            let body = harvest_val fuel ty (E.Dereference p) in
            if body = [] then []
            else sole_owner p (body @ [S.Expression (dot0 p "reset")])
          and harvest_ind fuel g args e =
            (* Mutual blocks would need a heterogeneous worklist; the mutual
               drain further down handles those for [Self] itself, but not for
               a mediator, so bail. *)
            (match g with
             | GlobRef.IndRef (kn, _) ->
               let mib = Global.lookup_mind kn in
               if Array.length mib.Declarations.mind_packets > 1 then
                 raise Harvest_bail
             | _ -> raise Harvest_bail);
            let ctors =
              match ind_ctor_tys g with
              | None -> raise Harvest_bail
              | Some c -> c
            in
            let g_ty = Miniml.Tglob (g, args, []) in
            let g_cpp = outer_ml g_ty in
            let self_recursive =
              List.exists
                (fun (_, ftys) -> List.exists (mentions g) ftys)
                ctors
            in
            (* Statements for one bare value [x] of [g args].  [on_spine], when
               given, diverts the mediator's own recursive fields to a local
               worklist instead of expanding them inline. *)
            let body_for on_spine x =
              let ctor_ref j = GlobRef.ConstructRef (
                (match g with
                 | GlobRef.IndRef (kn, i) -> (kn, i)
                 | _ -> raise Harvest_bail), j)
              in
              let field_stmts cname_str access ftys =
                List.concat
                  (List.mapi
                     (fun k fty ->
                       let inst = subst_targs args fty in
                       if not (contains_self inst) then []
                       (* [Crane BoxedFields]: a type-parameter field holding
                          [Self] is a [crane::field_box], a shared block, and a
                          shared block freed while another is being freed is
                          queued rather than freed in place (shared_block.h):
                          its destruction cannot recurse, so there is nothing
                          to drain. *)
                       else if boxes_param_field ~owner:g fty then []
                       else
                         let fe =
                           access
                             (Common.lookup_ctor_field_name ~owner:g cname_str k)
                         in
                         (* A field boxed for its own type is a pointer like a
                            recursive one. *)
                         let is_ptr = field_is_ptr g fty || boxes_field fty in
                         match on_spine with
                         | Some push
                           when is_ptr && outer_ml inst = g_cpp ->
                           push fe
                         | _ ->
                           if is_ptr then harvest_ptr (fuel - 1) inst fe
                           else harvest_val (fuel - 1) inst fe)
                     ftys)
              in
              let record_field_names =
                (* Rocq [Record]s are emitted as a plain struct whose members
                   are named after the projections, not as a variant with
                   generic [aN] constructor fields. *)
                match (ctors, Table.get_record_fields g) with
                | ([(_, ftys)], (_ :: _ as fs))
                  when List.length fs = List.length ftys ->
                  (try
                     Some (List.map
                             (function
                              | Some fr -> Common.pp_global_name Common.Term fr
                              | None -> raise Exit)
                             fs)
                   with Exit -> None)
                | _ -> None
              in
              match ctors with
              | [(_, ftys)] when record_field_names <> None ->
                let names = Option.get record_field_names in
                List.concat
                  (List.mapi
                     (fun k fty ->
                       let inst = subst_targs args fty in
                       if not (contains_self inst) then []
                       else
                         let fe =
                           E.Access
                             (Dot, x, Id.of_string_soft (List.nth names k))
                         in
                         if field_is_ptr g fty
                         then harvest_ptr (fuel - 1) inst fe
                         else harvest_val (fuel - 1) inst fe)
                     ftys)
              | [(j, ftys)] when Table.is_flat_inductive g ->
                (* Single-constructor "flat" inductives and records are laid
                   out as a plain struct: no variant, direct member access. *)
                let cname_str =
                  ctor_struct_name_of_ref ~fallback_idx:0 (ctor_ref j)
                in
                field_stmts cname_str (fun f -> E.Access (Dot, x, f)) ftys
              | _ ->
                List.concat_map
                  (fun (j, ftys) ->
                    let cref = ctor_ref j in
                    let cname_str =
                      ctor_struct_name_of_ref ~fallback_idx:(j - 1) cref
                    in
                    let av = Id.of_string (fresh_hv "_ha") in
                    let inner =
                      field_stmts cname_str (fun f ->
                        E.Access (Arrow, E.Local av, f) )
                        ftys
                    in
                    if inner = [] then []
                    else
                      [S.If_declaration {name = av; type_ = T.Pointer T.Auto; init = E.Variant_get_if (
                           T.Member (g_cpp, Id.of_string_soft cname_str),
                           E.Unary (Address_of, dot0 x "v_mut")); then_ = inner; else_ = []}])
                  ctors
            in
            if not self_recursive then body_for None e
            else begin
              let wl = fresh_hv "_hw" in
              let wl_id = Id.of_string wl in
              let pv = Id.of_string (wl ^ "p")
              and ev = Id.of_string (wl ^ "e") in
              let wl_ty =
                T.External
                  (Crane_rt.small_vector, [T.Shared_pointer (outer_ml g_ty)])
              in
              let push fe =
                [S.Expression (E.Access_call (Dot, 
                   E.Local wl_id, Id.of_string "push_back", [E.Move fe]))]
              in
              let on_spine = Some push in
              [S.Declare (wl_id, wl_ty, None)]
              @ body_for on_spine e
              @ [S.While (
                   E.Unary (Not, dot0 (E.Local wl_id) "empty"),
                   [ S.Bind_variable (pv, S.Binding.Declare (T.Auto, None),
                       E.Move (dot0 (E.Local wl_id) "back"));
                     S.Expression (dot0 (E.Local wl_id) "pop_back");
                     S.If {condition = E.Binary (Or, E.Unary (Not, E.Local pv),
                         E.Binary (Not_equal, dot0 (E.Local pv) "use_count",
                           E.Literal (Int 1))); then_ = [S.Continue]; else_ = []} ]
                   @ unique_fence
                   @ [S.Bind_variable (ev, S.Binding.Declare (T.Reference (Lvalue, T.Auto), None), E.Dereference (E.Local pv))]
                   @ body_for on_spine (E.Local ev))]
            end
          in
          (* Drain statements for a nested-mediator field, or [None] if the
             shape is one the harvester does not handle. *)
          let harvest_field field_id ml_ty =
            try
              let fe = E.Access (Arrow, E.Local _alt_id, field_id) in
              match harvest_ptr harvest_fuel ml_ty fe with
              | [] -> None
              | stmts -> Some stmts
            with Harvest_bail | Not_found -> None
          in
          (* Build drain statements for classified fields.  [Direct] fields
             move onto the worklist where this node owns them alone.
             [Wrapper] fields move the [Self]s of a uniquely-owned wrapper
             cell.  [List g] fields walk the list: a custom mapping (e.g.
             std::deque) through its [Drain] template or a range-for, a
             list-shaped inductive along its cons spine.  [Stmts] are the
             harvester's own statements. *)
          let mk_classified_field_stmts classified_fields =
            List.concat_map (fun (field_id, cls) ->
              let fe = E.Access (Arrow, E.Local _alt_id, field_id) in
              match cls with
              | `Stmts stmts -> stmts
              | `Direct ->
                (* Only a child this node owns alone would be freed with it;
                   any other is a decrement, done by the member's own
                   destructor, and never touches the worklist. *)
                [S.If {condition = E.Binary (And, fe, is_sole fe); then_ = [S.Expression (E.Access_call (Dot, 
                     E.Local _stack_id,
                     Id.of_string "push_back",
                     [E.Move fe]))]; else_ = []}]
              | `Wrapper wfields ->
                (* Reach through a uniquely-owned wrapper cell and move each
                   nested [Self] onto the worklist, then drop the cell. *)
                sole_owner fe
                  (List.map
                     (fun wf -> push_self_stmt (E.Access (Arrow, fe, wf)))
                     wfields
                   @ [S.Expression (dot0 fe "reset")])
              | `List list_g ->
                (* This iterative drain stands in for the naive recursive
                   destructor, so cleanup of a deep deque-backed recursive
                   value does not overflow the call stack (the primary CWE-674
                   mitigation;
                   regression: tests/regression/deque_deep_tree_stackoverflow).
                   Residual tradeoff (CWE-400): the drain heap-allocates one
                   [make_shared] wrapper per element, so under extreme memory
                   pressure an allocation inside this (noexcept) destructor can
                   still terminate the process.  Eliminating that would require
                   an allocation-free intrusive worklist -- a larger redesign
                   deferred here; bounded call-stack depth is the property that
                   matters for the adversarial-depth attack. *)
                if Table.is_custom list_g then
                  (* A [Drain "..."] clause on the custom container mapping spells
                     out how to iteratively yield children -- required for bare
                     value-type containers (deque, immer::flex_vector) that have
                     no [use_count]/[reset]. Without it we fall back to assuming a
                     smart-pointer-wrapped container. *)
                  begin match Table.find_custom_drain_opt list_g with
                  | Some tmpl ->
                    expand_drain_template
                      ~scrut:(Id.to_string _alt_id ^ "->"
                              ^ Id.to_string field_id)
                      ~self:(q_destr self_ty) tmpl
                  | None ->
                    let elem = Id.of_string "_elem" in
                    sole_owner fe
                      [ S.For_range (elem, E.Dereference fe,
                          [push_self_stmt (E.Local elem)]);
                        S.Expression (dot0 fe "reset") ]
                  end
                else
                  let ls = outer_ty (T.Entity_application (list_g, [self_ty], [])) in
                  let (_nil_s, cons_s) = list_ctor_struct_names list_g in
                  let cons_id = Id.of_string_soft cons_s in
                  let elem_field =
                    Common.lookup_ctor_field_name ~owner:list_g cons_s 0
                  in
                  let tail_field =
                    Common.lookup_ctor_field_name ~owner:list_g cons_s 1
                  in
                  let lp = Id.of_string "_lp" and lc = Id.of_string "_lc" in
                  let tail = E.Access (Dot, E.Local lc, tail_field) in
                  (* Walk the cons spine, moving each element onto the
                     worklist.  Ownership must be re-established at every cell,
                     not just the head: list cells share their tails through
                     [shared_ptr], so a suffix reachable from here may still be
                     owned by a live value.  Moving out of such a cell would gut
                     a list someone else is holding, so stop the walk as soon as
                     a tail is not uniquely owned -- the remaining cells then
                     die with their real owner. *)
                  sole_owner fe
                    [ S.Bind_variable (lp, S.Binding.Declare (T.Auto, None), dot0 fe "get");
                      S.While (
                        B.call
                          (E.Holds_alternative (T.Member (ls, cons_id)))
                          [arrow0 (E.Local lp) "v"],
                        [ S.Bind_variable (lc, S.Binding.Declare (T.Reference (Lvalue, T.Auto), None),
                            E.Variant_get (T.Member (ls, cons_id),
                              Some (arrow0 (E.Local lp) "v_mut")));
                          push_self_stmt
                            (E.Access (Dot, E.Local lc, elem_field));
                          S.If {condition = E.Binary (And, tail,
                              E.Binary (Equal, dot0 tail "use_count", E.Literal (Int 1))); then_ = (* The fence follows the [use_count] test rather
                               than preceding it -- see [unique_fence]. *)
                            unique_fence
                            @ [S.Bind_variable (lp, S.Binding.Existing, dot0 tail "get")]; else_ = [S.Break]} ]);
                      S.Expression (dot0 fe "reset") ]
              | _ -> []) classified_fields
          in
          (* For each constructor, classify recursive fields and build an
             [If_declaration] that uses [get_if] to test the variant alternative
             and drain recursive fields onto the stack.  Returns [Some stmt]
             for constructors with recursive fields, [None] otherwise.

             [parent_ty]    type to qualify the constructor in [get_if]
             [ctor_opt]     [Some ctor_id] for qualified access
                            ([typename Parent::Ctor]), [None] for bare
             [variant_var]  identifier of the variant to test *)
          let mk_ctor_drain parent_ty ctor_opt variant_var i tys_list cnames_arr =
            let classified_fields =
              List.filter_map
                (fun (j, ty) ->
                  let cls = classify_ml_self_ref ty in
                  let is_mutual = is_mutual_ref ty in
                  if cls <> `None || is_mutual then
                    let cname_str =
                      ctor_struct_name_of_ref ~fallback_idx:i cnames_arr.(i)
                    in
                    let field_id =
                      Common.lookup_ctor_field_name ~owner:cnames_arr.(i)
                        cname_str j
                    in
                    let effective_cls =
                      if is_mutual then `Direct else cls
                    in
                    match effective_cls with
                    | `Direct -> Some (field_id, `Direct)
                    (* A container whose elements are boxed holds the field
                       by value, not behind the pointer the fallback walk
                       takes apart, and a box gives its element out only to
                       read: with no [Drain] to say otherwise, the container
                       frees its children itself. *)
                    | `List g
                      when Table.is_custom g
                           && Table.find_custom_drain_opt g = None
                           && Table.find_boxed_wrapper_opt g <> None ->
                      None
                    | `List g -> Some (field_id, `List g)
                    | `Wrapper fs -> Some (field_id, `Wrapper fs)
                    | `Nested ml_ty ->
                      Option.map
                        (fun stmts -> (field_id, `Stmts stmts))
                        (harvest_field field_id ml_ty)
                    | _ -> None
                  else None)
                (List.mapi (fun j ty -> (j, ty)) tys_list)
            in
            match classified_fields with
            | [] -> None
            | _ ->
              let ctor_id =
                ctor_struct_id_of_ref ~fallback_idx:i cnames_arr.(i)
              in
              let ctor_arg = match ctor_opt with
                | None -> T.Named (ctor_id, [])
                | Some _ -> T.Member (parent_ty, ctor_id)
              in
              Some (S.If_declaration {name = _alt_id; type_ = T.Pointer T.Auto; init = E.Variant_get_if (ctor_arg,
                  E.Unary (Address_of, E.Local variant_var)); then_ = mk_classified_field_stmts classified_fields; else_ = []})
          in
          let drain_stmts =
            Array.to_list
              (Array.mapi
                 (fun i tys_list ->
                   mk_ctor_drain self_ty None _v_id i tys_list cnames)
                 tys)
            |> List.filter_map Fun.id
          in
          (* Each constructor holds at most one [Self] directly, and nothing
             else recursive: [Positive], [List], [Nat].  Destruction is a walk
             down one chain, with no worklist: take the child if this node
             owns it alone, let the node go, repeat.  A shared child is only
             a decrement and ends the walk. *)
          let linear_fields =
            let per_ctor =
              Array.to_list
                (Array.mapi
                   (fun i tys_list ->
                     let rec_fields =
                       List.filter_map
                         (fun (j, ty) ->
                           match classify_ml_self_ref ty, is_mutual_ref ty with
                           | `None, false -> None
                           | `Direct, false ->
                             let cname_str =
                               ctor_struct_name_of_ref ~fallback_idx:i cnames.(i)
                             in
                             Some
                               (Some
                                  ( ctor_struct_id_of_ref ~fallback_idx:i cnames.(i),
                                    Common.lookup_ctor_field_name ~owner:cnames.(i)
                                      cname_str j ))
                           | _ -> Some None )
                         (List.mapi (fun j ty -> (j, ty)) tys_list)
                     in
                     match rec_fields with
                     | [] -> Some []
                     | [Some f] -> Some [f]
                     | _ -> None )
                   tys)
            in
            if List.for_all Option.has_some per_ctor then
              Some (List.concat_map Option.get per_ctor)
            else None
          in
          match drain_stmts, linear_fields with
          | [], _ -> []
          | _, Some ((_ :: _) as fields) when not has_mutual ->
            let ptr_ty = T.Shared_pointer self_ty in
            let next_id = Id.of_string "_next" in
            let take (ctor_id, field_id) =
              let fe = E.Access (Arrow, E.Local _alt_id, field_id) in
              S.If_declaration {name = _alt_id; type_ = T.Pointer T.Auto; init = E.Variant_get_if (T.Named (ctor_id, []), E.Unary (Address_of, E.Local _v_id)); then_ = [ S.If {condition = E.Binary (And, fe, is_sole fe); then_ = unique_fence @ [S.Return (Some (E.Move fe))]; else_ = []} ]; else_ = []}
            in
            let next_lambda =
              lambda
                [(T.Reference (Lvalue, variant_t_ty), Some _v_id)]
                (Some ptr_ty)
                (List.map take fields @ [S.Return (Some (E.Literal Null_pointer))])
                ~capture:Runs_in_place
            in
            let body =
              [ S.Bind_variable (next_id, S.Binding.Declare (T.Auto, None), next_lambda);
                S.Bind_variable (_cur_id, S.Binding.Declare (ptr_ty, None),
                  B.call (E.Local next_id) [B.call (E.Local (Id.of_string "v_mut")) []]);
                S.While (E.Local _cur_id,
                  [ S.Bind_variable (_cur_id, S.Binding.Existing,
                      B.call (E.Local next_id)
                        [E.Access_call (Arrow, E.Local _cur_id, Id.of_string "v_mut", [])]) ]) ]
            in
            [(F.Destructor body, V.Public, Sec.Manipulators)]
          | _ when not has_mutual ->
            (* Self-recursive only: stack holds shared_ptr<Self> directly *)
            let stack_elem_ty = T.Shared_pointer self_ty in
            let stack_ty =
              T.External (Crane_rt.small_vector, [stack_elem_ty])
            in
            let _drain_id = Id.of_string "_drain" in
            let drain_lambda =
              lambda
                [(T.Reference (Lvalue, variant_t_ty), Some _v_id)]
                None drain_stmts ~capture:Runs_in_place
            in
            (* Most destroyed values own none of their children alone: they
               are temporaries that were moved from, or nodes whose children
               are shared with a newer version of the structure.  For a
               constructor whose recursive fields are all direct, such a value
               would push nothing onto the worklist, so it returns before the
               worklist is set up.  Constructors with other recursive fields
               always take the general path. *)
            let early_returns =
              Array.to_list
                (Array.mapi
                   (fun i tys_list ->
                     let fields =
                       List.filter_map
                         (fun (j, ty) ->
                           match classify_ml_self_ref ty, is_mutual_ref ty with
                           | `None, false -> None
                           | `Direct, false ->
                             let cname_str =
                               ctor_struct_name_of_ref ~fallback_idx:i cnames.(i)
                             in
                             Some
                               (Some
                                  (Common.lookup_ctor_field_name ~owner:cnames.(i)
                                     cname_str j))
                           | _ -> Some None)
                         (List.mapi (fun j ty -> (j, ty)) tys_list)
                     in
                     if not (List.for_all Option.has_some fields) then None
                     else
                       let owns_one =
                         List.fold_left
                           (fun acc f ->
                             let fe =
                               E.Access (Arrow, E.Local _alt_id, Option.get f)
                             in
                             let owned = E.Binary (And, fe, is_sole fe) in
                             match acc with
                             | None -> Some owned
                             | Some e -> Some (E.Binary (Or, e, owned)))
                           None fields
                       in
                       let ctor_id =
                         ctor_struct_id_of_ref ~fallback_idx:i cnames.(i)
                       in
                       let v_mut = B.call (E.Local (Id.of_string "v_mut")) [] in
                       match owns_one with
                       | None ->
                         Some
                           (S.If {condition = B.call
                                  (E.Holds_alternative (T.Named (ctor_id, [])))
                                  [v_mut]; then_ = [S.Return None]; else_ = []})
                       | Some e ->
                         Some
                           (S.If_declaration {name = _alt_id; type_ = T.Pointer T.Auto; init = E.Variant_get_if
                                  (T.Named (ctor_id, []), E.Unary (Address_of, v_mut)); then_ = [S.If {condition = E.Unary (Not, e); then_ = [S.Return None]; else_ = []}]; else_ = []}))
                   tys)
              |> List.filter_map Fun.id
            in
            let body =
              early_returns @
              [ S.Bind_variable (_stack_id, S.Binding.Declare (stack_ty, None),
                  E.Braced []);
                (* Most drains only ever hold a handful of pending nodes at
                   once (worklist depth tracks tree height, not size), so
                   [crane::small_vector] keeps the first 8 elements inline
                   with no heap allocation at all, spilling to a heap
                   std::vector only if a destructor happens to drain a
                   worklist deeper than that. *)
                S.Bind_variable (_drain_id, S.Binding.Declare (T.Auto, None), drain_lambda);
                S.Expression (B.call (E.Local _drain_id)
                  [B.call (E.Local (Id.of_string "v_mut")) []]);
                S.While (
                  E.Unary (Not,
                    E.Access_call (Dot, E.Local _stack_id,
                      Id.of_string "empty", [])),
                  [ S.Bind_variable (_cur_id, S.Binding.Declare (T.Auto, None),
                      E.Move (E.Access_call (Dot, E.Local _stack_id,
                        Id.of_string "back", [])));
                    S.Expression (E.Access_call (Dot, E.Local _stack_id,
                      Id.of_string "pop_back", []));
                    S.If {condition = E.Binary (Equal,
                        E.Access_call (Dot, E.Local _cur_id,
                          Id.of_string "use_count", []),
                        E.Literal (Int 1)); then_ = unique_fence
                      @ [S.Expression (B.call (E.Local _drain_id)
                        [E.Access_call (Arrow, E.Local _cur_id,
                          Id.of_string "v_mut", [])])]; else_ = []}
                  ])
              ]
            in
            [(F.Destructor body, V.Public, Sec.Manipulators)]
          | _, _ ->
            (* Mutual recursion: stack holds std::any to accommodate
               shared_ptrs of different types in the mutual group *)
            let stack_ty =
              T.External (Crane_rt.small_vector, [T.Any])
            in
            let _drain_self_id = Id.of_string "_drain_self" in
            let drain_self_lambda =
              lambda
                [(T.Reference (Lvalue, variant_t_ty), Some _v_id)]
                None drain_stmts ~capture:Runs_in_place
            in
            (* Build the per-partner drain logic used inside the while loop.
               For each partner type, generates an [If_declaration] that casts the
               [std::any] stack entry to [shared_ptr<Partner>], then drains
               the partner's recursive fields into the shared stack. *)
            let gen_partner_branch (pname, pcnames, ptys, _) =
              let partner_ty = T.Entity_application (pname, ty_vars, []) in
              let partner_drains =
                Array.to_list
                  (Array.mapi
                     (fun pi ptys_list ->
                       mk_ctor_drain partner_ty (Some ()) _pv_id
                         pi ptys_list pcnames)
                     ptys)
                |> List.filter_map Fun.id
              in
              (partner_ty, partner_drains)
            in
            let partner_branches =
              List.map gen_partner_branch mutual_partners
            in
            (* Build the chained if/else-if for any_cast branches in the loop.
               Self branch: any_cast<shared_ptr<Self>>, call _drain_self.
               Partner branches: any_cast<shared_ptr<Partner>>, inline drain. *)
            let deref_sp = E.Dereference (E.Local _sp_id) in
            let sp_alive_and_unique =
              E.Binary (And, deref_sp,
                E.Binary (Equal,
                  E.Access_call (Dot, deref_sp,
                    Id.of_string "use_count", []),
                  E.Literal (Int 1)))
            in
            let self_branch_body =
              [S.If {condition = sp_alive_and_unique; then_ = unique_fence
                @ [S.Expression (B.call (E.Local _drain_self_id)
                  [E.Access_call (Arrow, deref_sp,
                    Id.of_string "v_mut", [])])]; else_ = []}]
            in
            let rec build_if_chain branches =
              match branches with
              | [] -> []
              | (partner_ty, partner_drains) :: rest ->
                let inner = build_if_chain rest in
                let partner_body =
                  [S.If {condition = sp_alive_and_unique; then_ = S.Bind_variable (_pv_id, S.Binding.Declare (T.Reference (Lvalue, T.Auto), None),
                      E.Access_call (Arrow, deref_sp,
                        Id.of_string "v_mut", []))
                    :: partner_drains; else_ = []}]
                in
                [S.If_declaration {name = _sp_id; type_ = T.Pointer T.Auto; init = Cpp_erasure.unbox_ir (T.Shared_pointer partner_ty)
                    (E.Unary (Address_of, E.Local _cur_id)); then_ = partner_body; else_ = inner}]
            in
            let loop_body_stmts =
              [S.If_declaration {name = _sp_id; type_ = T.Pointer T.Auto; init = Cpp_erasure.unbox_ir (T.Shared_pointer self_ty)
                  (E.Unary (Address_of, E.Local _cur_id)); then_ = self_branch_body; else_ = build_if_chain partner_branches}]
            in
            let body =
              [ S.Bind_variable (_stack_id, S.Binding.Declare (stack_ty, None), E.Braced []);
                S.Bind_variable (_drain_self_id, S.Binding.Declare (T.Auto, None), drain_self_lambda);
                S.Expression (B.call (E.Local _drain_self_id)
                  [B.call (E.Local (Id.of_string "v_mut")) []]);
                S.While (
                  E.Unary (Not,
                    E.Access_call (Dot, E.Local _stack_id,
                      Id.of_string "empty", [])),
                  S.Bind_variable (_cur_id, S.Binding.Declare (T.Auto, None),
                    E.Move (E.Access_call (Dot, E.Local _stack_id,
                      Id.of_string "back", [])))
                  :: S.Expression (E.Access_call (Dot, E.Local _stack_id,
                       Id.of_string "pop_back", []))
                  :: loop_body_stmts)
              ]
            in
            [(F.Destructor body, V.Public, Sec.Manipulators)]
      in

      (* For coinductive types, add public constructor accepting
         std::function<variant_t()> (public so make_shared can access it) *)
      let lazy_ctor =
        if is_coinductive then
          let param_name = Id.of_string "_thunk" in
          let param_ty = T.Function ([], variant_alias_ty) in
          let init_expr =
            B.call
              (E.Local
                 (Id.of_string_soft
                    (Crane_rt.lazy_ ^ "<" ^ variant_alias_name ^ ">") ))
              [E.Move (E.Local param_name)]
          in
          let init_list = [(vmn_id, init_expr)] in
          [
            constructor [(param_name, param_ty)] init_list;
          ]
        else
          []
      in

      (* 5. Static factory methods.  Each constructor gets one factory
         method as a direct static member of the struct, returning by value.

         Factory names are the lowercase of the constructor struct name
         (e.g., Cons → cons).  If this collides with a C++ keyword, the
         type's own name or a type its module declares, the factory falls
         back to PascalCase with trailing underscore (e.g., Char → Char_).
         See {!Translation_support.factory_name_of_ctor}.

         Move semantics: parameters use the "sink parameter" idiom (passed by
         value, std::move'd into the struct initializer unless trivially
         copyable).  Non-coinductive fields stored behind a pointer take the
         inner type by value and are allocated internally (make_shared, or
         the arena-aware factory); a coinductive's take the value type by
         [const &]. *)
      let mk_factory_methods ret_ty build i tys_list =
        let c = cnames.(i) in
        let cname = ctor_struct_name_of_ref ~fallback_idx:i c in
        let fname = factory_name_of_ctor ~fallback_idx:i c in
        let factory_name = Id.of_string fname in
        (* Convert ML types both as public API types and constructor storage
           types.  Public APIs remain value-shaped (empty ns); storage uses
           [name] in ns so non-coinductive recursive occurrences are
           [shared_ptr]-wrapped. *)
        let cpp_tys =
          List.mapi
            (fun j ty ->
              (* The field as the struct declares it. *)
              let storage_ty = compute_field_cpp_ty ty in
              let api_ty =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  vars
                  ty
              in
              let api_ty =
                if vars = [] then
                  match api_ty with
                  | Tshared_ptr _ ->
                    tvar_erase_type api_ty
                  | _ when has_unnamed_tvar api_ty -> Tany
                  | _ -> api_ty
                else api_ty
              in
              (j, storage_ty, api_ty) )
            tys_list
        in
        (* Derive factory parameter name from the registered field name.
           Factory params use the bare binder name (e.g. [left]) rather than
           the prefixed field name (e.g. [d_left]), since they are function
           parameters, not struct members.  Falls back to the full field id
           if stripping the [d_] prefix fails. *)
        let param_name_of j =
          let field_id = lookup_ctor_field_name ~owner:name cname j in
          let s = Id.to_string field_id in
          if String.length s > 2 && s.[0] = 'd' && s.[1] = '_' then
            Id.of_string (String.sub s 2 (String.length s - 2))
          else field_id
        in
        (* For owned recursive fields in value-type inductives, factory
           params take the inner value by value (sink parameter) so callers
           can move in.  A coinductive's pointer fields take the value type
           by const reference. *)
        let params =
          List.map
            (fun (j, storage_ty, api_ty) ->
              let param_ty =
                match storage_ty with
                | Tshared_ptr _ ->
                  if is_coinductive then Tref (Lvalue, Tconst api_ty)
                  else api_ty
                | _ -> api_ty
              in
              (param_name_of j, param_ty) )
            cpp_tys
        in
        let lower_params = List.map (fun (x, t) -> (x, lower_type t)) in
        (* A conversion between the parameter and its field reads the
           parameter for the last time, and takes it by move where it reads
           it once, outside any closure. *)
        let sink_converted api_ty var e =
          (* The parameter's reads in [e], each in a closure or a statement
             counting as two. *)
          let rec reads ~weight n e =
            match e with
            | CPPvar _ when e = var -> n + weight
            | CPPlambda _ -> fold_expr_children ~on_expr:(reads ~weight:2) ~on_stmts:(stmt_reads ~weight:2) n e
            | _ -> fold_expr_children ~on_expr:(reads ~weight) ~on_stmts:(stmt_reads ~weight:2) n e
          and stmt_reads ~weight n ss =
            List.fold_left
              (fun n s -> fold_stmt_children ~on_expr:(reads ~weight) ~on_stmts:(stmt_reads ~weight) n s)
              n ss
          in
          if is_trivially_copyable_type api_ty || reads ~weight:1 0 e <> 1 then e
          else
            let rec moved e =
              match e with
              | CPPvar _ when e = var -> CPPmove var
              | _ -> map_expr moved Fun.id Fun.id e
            in
            moved e
        in
        (* The argument each field is built from.  A conversion is a
           translation result, converted where the argument takes it. *)
        let ctor_args =
          List.map
            (fun (j, storage_ty, api_ty) : Cpp_ir.Lowered.Expr.t ->
              let var = CPPvar (param_name_of j) in
              let local : Cpp_ir.Lowered.Expr.t = E.Local (param_name_of j) in
              match storage_ty with
              | Tfun (storage_args, storage_ret) -> begin
                match api_ty with
                | Tfun (api_args, api_ret) when List.length storage_args = List.length api_args
                  && storage_ty <> api_ty ->
                  let lambda_params =
                    List.mapi
                      (fun k storage_arg ->
                        (lower_type storage_arg, Some (Id.of_string ("x" ^ string_of_int k)))
                      )
                      storage_args
                  in
                  let call_args =
                    List.mapi
                      (fun k (_storage_arg, api_arg) ->
                        let arg_var =
                          CPPvar (Id.of_string ("x" ^ string_of_int k))
                        in
                        if _storage_arg = api_arg then
                          arg_var
                        else
                          gen_type_conversion_expr
                            ~src_ty:_storage_arg ~dst_ty:api_arg
                            arg_var )
                      (List.combine storage_args api_args)
                  in
                  let call = mk_call var call_args in
                  let ret =
                    if storage_ret = api_ret then
                      call
                    else
                      gen_type_conversion_expr
                        ~src_ty:api_ret ~dst_ty:storage_ret
                        call
                  in
                  (* The lambda's result is the storage-side type by
                     construction -- [ret] is the call converted into it.  Say
                     so, rather than leaving a later pass to read it back off
                     the body. *)
                  lambda lambda_params (Some (lower_type storage_ret))
                    [S.Return (Some (lower_expr ret))] ~capture:Stored
                | _ when storage_ty = api_ty -> E.Move local
                | _ ->
                  lower_expr
                    (sink_converted api_ty var
                       (gen_type_conversion_expr ~src_ty:api_ty ~dst_ty:storage_ty var))
              end
              | Tshared_ptr inner ->
                let arg = if is_coinductive then var else CPPmove var in
                let converted =
                  if inner = api_ty then arg
                  else gen_type_conversion_expr ~src_ty:api_ty ~dst_ty:inner arg
                in
                (* A single factory call.  For arena-eligible types this is
                   the runtime-arena-aware factory ([Arena_scoped]:
                   crane::rc<T>::make / crane::arena_make_shared), which
                   bump-allocates only when a scope is open and otherwise is
                   exactly make_shared/make_rc; NoArena / coinductive / mutual
                   types keep the plain factory. *)
                if arena_runtime_ok then
                  B.call (E.Allocate (Arena_scoped, lower_type inner)) [lower_expr converted]
                else
                  B.call (E.Allocate (Heap, lower_type inner)) [lower_expr converted]
              | _ when storage_ty = api_ty ->
                if is_trivially_copyable_type api_ty then local
                else E.Move local
              | _ ->
                lower_expr
                  (sink_converted api_ty var
                     (gen_type_conversion_expr ~src_ty:api_ty ~dst_ty:storage_ty var)) )
            cpp_tys
        in
        (* Under [Crane NonAtomicRc], a field holding the inductive itself
           takes a [crane::child_slot]: a value, which it boxes, sharing one
           cell between all values of a constructor without fields, or a
           [crane::child] reference to the cell of a field read out of a
           matched value, which the new node shares.  Rebuilding a path in a
           persistent tree then allocates only the nodes on the path.  Not
           for arena allocation, nor for coinductive or shared-variant types,
           whose cells are made differently. *)
        let child_field (_, storage_ty, _) ty =
          Table.non_atomic_rc () && (not is_coinductive) && (not arena_runtime_ok)
          && (not (Table.is_shared_variant name))
          && is_ref_to name vars ty
          && (match storage_ty with Tshared_ptr _ -> true | _ -> false)
        in
        let fields = List.combine cpp_tys tys_list in
        let primary_params =
          List.map2
            (fun ((_, storage_ty, _) as f, ty) (pname, pty) ->
              match storage_ty with
              | Tshared_ptr inner when child_field f ty ->
                (pname, Tid_external (Crane_rt.child_slot, [inner]))
              | _ -> (pname, pty) )
            fields params
        in
        let primary_ctor_args =
          List.map2
            (fun (((j, _, _) as f), ty) arg : Cpp_ir.Lowered.Expr.t ->
              if child_field f ty then
                E.Access_call (Dot, E.Local (param_name_of j), Id.of_string "take", [])
              else arg )
            fields ctor_args
        in
        let body = [S.Return (Some (build i cname primary_ctor_args))] in
        let primary : Cpp_ir.Lowered.phase F.member =
          ( Method
              (static_method ~name:factory_name ~ret:ret_ty ~params:(lower_params primary_params) ~body),
            V.Public,
            Sec.Creators )
        in
        (* Perceus reuse factory (Crane Reuse): a variant [<ctor>__reuse] that
           takes a leading reuse-token parameter [_tok] and, for the first
           field holding the inductive itself, allocates via
           [crane::make_rc_reusing(_tok, ...)] instead of make_shared/arena_make
           -- recycling the token's cell in place when it is uniquely owned.
           The other boxed fields allocate as before.  Only for NonAtomicRc
           (crane::rc carries the reusable control block) and non-coinductive
           constructors with such a field; the caller (a reuse-eligible match
           arm) threads a matched, uniquely-owned recursive child as the
           token. *)
        let token_field =
          List.find_map
            (fun ((j, storage_ty, _), ty) ->
              match (storage_ty, Mlutil.ml_resolve ty) with
              | Tshared_ptr inner, Miniml.Tglob (r, _, _)
                when GlobRef.CanOrd.equal r name ->
                Some (j, inner)
              | _ -> None )
            (List.combine cpp_tys tys_list)
        in
        (* A shared variant's reuse factory takes the matched value itself as
           the token: where its block is unique and holds this alternative,
           the new fields are written into it ([shared_variant::try_reuse]);
           otherwise the value is built as [<ctor>] builds it.  The test is
           the factory's, so a match arm needs no path of its own. *)
        let shared_reuse_factory () : Cpp_ir.Lowered.phase F.member list =
          let tok_id = Id.of_string "_tok" and alt_id = Id.of_string "_alt" in
          let reused : Cpp_ir.Lowered.Expr.t =
            E.Access_call
              ( Dot,
                E.Access (Dot, E.Local tok_id, Id.of_string "v_"),
                Id.of_string "try_reuse",
                [E.Move (E.Local alt_id)] )
          in
          let body =
            [ S.Bind_variable
                ( alt_id,
                  S.Binding.Declare (T.Auto, None),
                  E.Local_aggregate {struct_ = Id.of_string cname; type_args = []; values = ctor_args} );
              S.If {condition = reused; then_ = [S.Return (Some (E.Local tok_id))]; else_ = []};
              S.Return (Some (build i cname [E.Move (E.Local alt_id)])) ]
          in
          [ ( Method
                (static_method
                   ~name:(Generated_name.companion (Id.of_string fname) "reuse")
                   ~ret:ret_ty ~params:((tok_id, ret_ty) :: lower_params params) ~body),
              V.Public,
              Sec.Creators ) ]
        in
        let reuse_factory : Cpp_ir.Lowered.phase F.member list =
          if Table.reuse () && (not is_coinductive) && Table.is_shared_variant name then
            (* A constructor with no fields has no block to write into. *)
            if tys_list = [] then [] else shared_reuse_factory ()
          else
          match token_field with
          | Some (tok_j, rec_inner)
            when Table.reuse () && Table.non_atomic_rc () && (not is_coinductive)
                 (* A shared variant's slot holds no cell to recycle. *)
                 && not (Table.is_shared_variant name) ->
              let tok_id = Id.of_string "_tok" in
              let reuse_params =
                (tok_id, Tshared_ptr rec_inner) :: params
              in
              let reuse_ctor_args =
                List.map2
                  (fun (j, _, _) (a : Cpp_ir.Lowered.Expr.t) ->
                    match a with
                    | Call (_, Allocate (Heap, inner), cargs)
                    | Call (_, Allocate (Arena_scoped, inner), cargs)
                      when j = tok_j ->
                      (* make_rc_reusing takes the token first. *)
                      B.call (E.Allocate (Reusing, inner))
                        (E.Move (E.Local tok_id) :: cargs)
                    | other -> other )
                  cpp_tys ctor_args
              in
              let reuse_body = [S.Return (Some (build i cname reuse_ctor_args))] in
              [ ( Method
                    (static_method
                       ~name:(Generated_name.companion (Id.of_string fname) "reuse")
                       ~ret:ret_ty ~params:(lower_params reuse_params) ~body:reuse_body),
                  V.Public,
                  Sec.Creators ) ]
          | _ -> []
        in
        primary :: reuse_factory
      in
      let factory_methods =
        List.flatten
          (Array.to_list
             (Array.mapi
                (mk_factory_methods self_ty
                   (* Build alternative [i] from the factory's arguments, in
                      the parent type's explicit constructor: O{} → Nat(O{}).
                      A coinductive's alternative is built inside its new
                      lazy cell, from the arguments themselves: no move
                      through the alternative, the variant and the cell on
                      the way in.  Use CPPglob with the inductive ref so
                      the printer emits the correct name (handles both
                      top-level and module-nested inductives).  The type
                      arguments must be spelled out: when the inductive is
                      not merged into its wrapper struct, the name reached
                      through the wrapper ([List::list]) is no longer the
                      injected-class-name, so class template argument
                      deduction is not available. *)
                   (fun i cname args : Cpp_ir.Lowered.Expr.t ->
                     let self = lower_expr (mk_cppglob name (List.map named_tvar vars)) in
                     if is_coinductive then
                       B.call self
                         [B.call lazy_cell (E.In_place :: E.In_place_index i :: args)]
                     else
                       B.call self
                         [E.Local_aggregate {struct_ = Id.of_string cname; type_args = []; values = args}] ) )
                tys ) )
      in

      (* For coinductive types, the [lazy_] factory: the value [thunk]
         returns, once it is asked for.  The thunk yields a whole coinductive
         value, so the new cell delegates to that value's cell rather than
         copying its variant out, and the callable goes into the one closure
         block as it is: [F] is the caller's own closure type, not a
         [crane::fn] wrapped around it. *)
      let lazy_factory =
        if is_coinductive then
          let f = Id.of_string "F" in
          let thunk = Id.of_string "thunk" in
          let cell_ty = T.External (Crane_rt.lazy_, [variant_alias_ty]) in
          let delegate =
            B.call
              (E.Scope (lazy_cell, Id.of_string "delegate", []))
              [E.Forward (B.named_variable f, E.Local thunk)]
          in
          let body =
            [S.Return (Some (B.call (lower_expr (mk_cppglob name (List.map named_tvar vars))) [delegate]))]
          in
          let m =
            { (static_method ~name:(Id.of_string "lazy_") ~ret:self_ty
                 ~params:[(thunk, T.Reference (Forwarding, B.named_variable f))] ~body)
              with type_params = [(Typename, f)] }
          in
          (* The cell the factory builds a value around. *)
          let cell_ctor =
            let c = Id.of_string "_cell" in
            constructor [(c, cell_ty)] [(vmn_id, E.Move (E.Local c))]
          in
          [cell_ctor; (Method m, V.Public, Sec.Creators)]

        else
          []
      in

      (* No deep-copy constructor: recursive fields, arena-backed or not, are
         ordinary refcounted smart pointers, so the implicit copy is correct
         and O(1) per node.  What remains is the converting constructor from
         another instantiation of the same template. *)
      let value_copy_clone_methods =
          let converting_ctor =
            let all_fields_empty =
              Array.for_all (fun tys_list -> tys_list = []) tys
            in
            (* Arena-backed types are ordinary recursive smart-pointer types,
               so the cross-instantiation converting constructor is generated
               for them exactly as for any other polymorphic type. *)
            if vars = [] || all_fields_empty then []
            else
              let n_vars = List.length vars in
              let u_var_names =
                List.mapi (fun i _ -> Generated_name.member "U" ~of_:n_vars i) vars
              in
              let u_tys =
                List.map B.named_variable u_var_names
              in
              let source_ty = T.Entity_application (name, u_tys, []) in
              let n_ctors = Array.length cnames in
              let other_id = Id.of_string "_other" in
              let vmn_id = Id.of_string variant_member_name in
              let gen_branch i tys_list =
                let c = cnames.(i) in
                let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                let ctor_struct_name =
                  ctor_struct_name_of_ref ~fallback_idx:i c
                in
                let field_info =
                  List.mapi
                    (fun j ty ->
                      let field_id =
                        lookup_ctor_field_name ~owner:c ctor_struct_name j
                      in
                      let make_field_ty var_names = field_storage_ty var_names ty in
                      (* A promoted parameter -- [ptr] in [Dvalue_base<ptr,
                         iptr>], from the instance in scope where the
                         inductive was declared -- leads [vars], and a field
                         of its type is spelled by its own name whatever the
                         names given for the variables.  It is a template
                         parameter here like any other: the variable in its
                         position, [_U0] on the source side. *)
                      let promoted_as var_names t =
                        let promoted =
                          match name with
                          | GlobRef.IndRef (kn, _) -> Table.ind_promoted_params kn
                          | _ -> []
                        in
                        let name_at id =
                          let rec find k = function
                            | [] -> None
                            | p :: rest ->
                              if Id.equal p id then List.nth_opt var_names k
                              else find (k + 1) rest
                          in
                          find 0 promoted
                        in
                        map_cpp_type
                          (function
                            | (Tvar (Tv_index (_, Some id) | Tv_named id) | Tpromoted id) as t -> (
                              match name_at id with
                              | Some u -> Tvar (Tv_named u)
                              | None -> t )
                            | t -> t )
                          t
                      in
                      let src_fty =
                        promoted_as u_var_names
                          (deapply_families name u_var_names
                             (make_field_ty u_var_names) )
                      in
                      let dst_fty =
                        promoted_as vars
                          (deapply_families name vars (make_field_ty vars))
                      in
                      (field_id, src_fty, dst_fty))
                    tys_list
                in
                let converted =
                  List.map
                    (fun (field_id, src_fty, dst_fty) ->
                      (* A [crane::field] converts as what it holds: read it
                         unboxed, and the struct's constructor boxes the
                         result again where that pays. *)
                      let src_expr, src_fty, dst_fty =
                        let unboxed = function
                          | Tid_external (f, [t]) when String.equal f Crane_rt.field -> Some t
                          | _ -> None
                        in
                        match (unboxed src_fty, unboxed dst_fty) with
                        | Some s, Some d ->
                          ( mk_call (CPPrt Crane_rt.Unbox_field) [CPPvar field_id],
                            s, d )
                        | _ -> (CPPvar field_id, src_fty, dst_fty)
                      in
                      (* A translation result, converted where the branch
                         takes it. *)
                      lower_expr @@ gen_type_conversion_expr

                        (* Every inductive generated into this same scope --
                           the type itself, its mutual siblings, and any other
                           module-local inductive -- is spelled bare here, so
                           it must not be namespace-qualified. *)
                        ~skip:(fun g ->
                          GlobRef.CanOrd.equal g name
                          || Table.same_mutual_block g name
                          || spells_bare g)
                        ~src_ty:src_fty ~dst_ty:dst_fty
                        src_expr)
                    field_info
                in
                (cname_id, field_info, converted)
              in
              let branches =
                List.init n_ctors (fun i -> gen_branch i tys.(i))
              in
              (* Each branch returns the source's alternative read at this
                 instantiation; see [init] below. *)
              let make_branch_body cname_id field_info converted =
                match field_info with
                | [] -> [S.Return (Some (E.Local_aggregate {struct_ = cname_id; type_args = []; values = []}))]
                | _ ->
                  (* The alternative is named exactly as the
                     [std::holds_alternative] guard names it. *)
                  [ S.Structured_binding
                      ( List.map (fun (id, _, _) -> id) field_info,
                        E.Variant_get
                          ( T.Member (source_ty, cname_id),
                            Some (E.Access_call (Dot, E.Local other_id, Id.of_string "v", [])) ) );
                    S.Return (Some (E.Local_aggregate {struct_ = cname_id; type_args = []; values = converted})) ]
              in
              let body =
                if n_ctors = 1 then
                  let cname_id, field_info, converted =
                    List.hd branches
                  in
                  make_branch_body cname_id field_info converted
                else
                  (* Build if/else if/else chain *)
                  let other_v =
                    E.Access_call (Dot, E.Local other_id,
                                       Id.of_string "v", [])
                  in
                  let rec build_if_chain = function
                    | [] -> CErrors.anomaly (Pp.str "converting constructor: empty constructor list")
                    | [(cname_id, field_info, converted)] ->
                      (* Last branch: no guard *)
                      make_branch_body cname_id field_info converted
                    | (cname_id, field_info, converted) :: rest ->
                      let guard =
                        B.call
                          (E.Holds_alternative
                             (T.Member (source_ty, cname_id)))
                          [other_v]
                      in
                      let body =
                        make_branch_body cname_id field_info converted
                      in
                      [S.If {condition = guard; then_ = body; else_ = build_if_chain rest}]
                  in
                  build_if_chain branches
              in
              (* The source instantiation is the same template as the
                 destination, so its arguments have the same kinds: a
                 [template <typename> class] parameter cannot be stood in for
                 by a plain [typename]. *)
              let tparams =
                List.mapi
                  (fun i u ->
                    let tt : Cpp_ir.Lowered.phase Cpp_ir.Template.Parameter_kind.t =
                      match List.nth_opt type_params i with
                      | Some (tt, _) -> tt
                      | None -> Typename
                    in
                    (tt, u) )
                  u_var_names
              in
              let ctor_params =
                [(other_id,
                  T.Reference (Lvalue, T.Const source_ty))]
              in
              (* The variant is initialised, not assigned: default-constructing
                 it first needs the first alternative's fields to have a
                 default, and a field that is a tree does not.  A coinductive
                 value converts when it is forced, so the conversion is its
                 thunk, holding a copy of the source. *)
              let convert_variant ~capture =
                lambda [] (Some variant_alias_ty) body ~capture
              in
              let init =
                if is_coinductive then
                  (* Through [converted_from]: a conversion back to the type
                     the source came from is the source's own cell. *)
                  B.call
                    (E.Local
                       (Id.of_string_soft
                          (Crane_rt.lazy_ ^ "<" ^ variant_alias_name
                          ^ ">::converted_from") ))
                    [ B.call (E.Access (Dot, E.Local other_id, Id.of_string "lazy_cell")) [];
                      convert_variant ~capture:Stored ]
                else B.call (convert_variant ~capture:Runs_in_place) []
              in
              (* Non-explicit: erased grammar actions produce a [List<std::any>]
                 that must implicitly recover to the concrete-element list at
                 return/assignment sites (e.g. [nt_semty] = [list (string *
                 json_value)]).  An [explicit] converting ctor makes those sites
                 fail with "no viable conversion".  Element recovery is a guarded
                 per-element [any_cast], so allowing the implicit conversion is
                 safe for well-typed extracted code. *)
              [constructor ~tparams ~explicit:false ctor_params [(vmn_id, init)]]
          in
          converting_ctor
      in

      (* A coinductive's lazy cell, for the converting constructor of another
         instantiation of the same template: a conversion that returns to the
         type its source was itself converted from reuses the source's cell
         ([crane::lazy::converted_from]) rather than wrapping it again. *)
      let lazy_cell_accessor =
        if not is_coinductive then []
        else
          [ accessor ~no_pure:false "lazy_cell"
              (T.Const (T.Reference (Lvalue, T.External (Crane_rt.lazy_, [variant_alias_ty]))))
              [S.Return (Some (E.Local vmn_id))] ]
      in
      (* Add public accessor for v_ to enable pattern matching from outside *)
      let v_accessor =
        if is_coinductive then
          (* For coinductive: const variant_t& v() const { return
             lazy_v_.force(); } *)
          accessor ~no_pure:false "v"
            (T.Const (T.Reference (Lvalue, variant_alias_ty)))
            [ S.Return
                (Some (B.call (E.Access (Dot, E.Local vmn_id, Id.of_string "force")) [])) ]
        else (* For inductive: const variant_t& v() const { return v_; } *)
          accessor ~no_pure:false "v"
            (T.Const (T.Reference (Lvalue, variant_alias_ty)))
            [S.Return (Some (E.Local vmn_id))]
      in

      (* Mutable accessor, for in-place reuse of a uniquely-owned value and
         for the iterative destructor's drains.  For non-coinductive types:
         variant_t& v_mut() { return v_; }.  Not generated for coinductive
         types (lazy evaluation complicates reuse). *)
      let v_mut_accessor =
        if is_coinductive then
          []
        else
          [ accessor ~is_const:false ~is_inline:true ~section:Manipulators ~no_pure:true "v_mut"
              (T.Reference (Lvalue, variant_alias_ty))
              [S.Return (Some (E.Local vmn_id))] ]
      in

      (* 6. Generate methods from method candidates using shared helper *)
      let method_fields =
        gen_methods name vars method_candidates
      in

      (* Detect if any method contains shared_from_this (i.e., returns 'this').
         If so, the struct needs to inherit from
         std::enable_shared_from_this. *)
      let needs_shared_from_this =
        List.exists
          (fun ((fld : Cpp_ir.Lowered.phase F.t), _vis, _tag) ->
            match fld with
            | Method {body; _} ->
              List.exists stmt_has_shared_from_this body
            | _ -> false )
          method_fields
      in

      (* Categorize user methods: const methods are ACCESSORS, non-const are
         MANIPULATORS *)
      let method_fields =
        List.map
          (fun ((fld : Cpp_ir.Lowered.phase F.t), vis, _tag) ->
            match fld with
            | Method {receiver = Instance {is_const = true; _}; _} ->
              (fld, vis, Sec.Accessors)
            | Method _ -> (fld, vis, Sec.Manipulators)
            | _ -> (fld, vis, Sec.Untagged) )
          method_fields
      in
      (* Split methods into manipulators and accessors *)
      let method_manipulators =
        List.filter (fun (_, _, tag) -> tag = Sec.Manipulators) method_fields
      in
      let method_accessors =
        List.filter (fun (_, _, tag) -> tag <> Sec.Manipulators) method_fields
      in

      (* BDE field ordering: public: constructor structs, variant_using,
         element_using (TYPES)
         private: variant_member (DATA)
         public: default_ctor + public_ctors + converting ctor + lazy_ctor +
         factory methods + lazy_factory (CREATORS),
         destructor + defaulted special members + v_mut + manipulators
         (MANIPULATORS),
         v_accessor + lazy_cell_accessor + const methods (ACCESSORS) *)
      let all_fields =
        constructor_structs
        @ [variant_using]
        @ element_using
        @ [variant_member]
        @ default_ctor
        @ public_ctors
        @ value_copy_clone_methods
        @ lazy_ctor
        @ factory_methods
        @ lazy_factory
        @ iterative_destructor
        (* A user-declared destructor (the iterative drain above) suppresses the
           implicit move ctor/assign, which silently turns every [std::move] of
           this value into a refcount-bumping copy.  Re-default all copy/move
           special members so moves stay cheap (and Perceus reuse can observe
           [use_count()==1]).  Emitted whenever we declare a custom destructor,
           for every extraction: the suppression is a property of the *type*,
           so reuse-off code pays the same needless refcount traffic that reuse
           needs eliminated.  Real moves expose code that reads a value after
           moving from it, which a copy fallback would hide: the loop
           lowering therefore never moves from invariant parameters,
           prvalues or borrowed cells. *)
        @ (match iterative_destructor with
           | _ :: _ -> [(F.Defaulted_special_members, V.Public, Sec.Manipulators)]
           | [] -> [])
        @ v_mut_accessor
        @ method_manipulators
        @ [v_accessor]
        @ lazy_cell_accessor
        @ method_accessors
      in

      (* Just the struct itself - no extra namespace wrapper *)
      (Struct
         { ref_ = name;
           fields = all_fields;
           type_params;
           constraint_ = None;
           needs_shared_from_this }
        : Cpp_ir.Lowered.Decl.t)


(** Generate methods for eponymous records: the record's fields are merged
    into its module's struct, and the functions taking the record become
    instance methods of that struct ({!gen_methods} with [~merged:true]).
    @param name the record's [GlobRef] (e.g. the [IndRef] of [CHT])
    @param vars the record's type variables (e.g. [[K; V]] for [CHT<K, V>])
    @param method_candidates
      functions to generate as methods: [(func_ref, body, type, this_pos)] *)
let gen_record_methods (name : GlobRef.t) (vars : Id.t list) method_candidates =
  gen_methods ~merged:true name vars method_candidates
 
