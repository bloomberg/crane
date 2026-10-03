(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Inductive types: methods generated onto an inductive's struct, and the
    struct itself -- constructors, factories, conversions, and the iterative
    destructor. *)

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
let replace_this_in_lambdas self_type stmts =
  let id_type ty = ty in
  let self_id = Id.of_string "_self" in
  (* Check if CPPthis or CPPshared_from_this appears in an expression. *)
  let rec expr_has_this = function
    | CPPthis | CPPshared_from_this _ -> true
    | e ->
      let found = ref false in
      ignore (map_expr (fun e' ->
        if expr_has_this e' then found := true; e') (fun s -> s) id_type e);
      !found
  in
  (* Check if CPPthis or CPPshared_from_this appears in statements. *)
  let rec stmt_has_this = function
    | s ->
      let found = ref false in
      ignore (map_stmt
        (fun e -> if expr_has_this e then found := true; e)
        (fun s' -> if stmt_has_this s' then found := true; s')
        id_type s);
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
        id_type e);
      !found
  and lambda_captures_this_stmt s =
    let found = ref false in
    ignore (map_stmt
      (fun e -> if lambda_captures_this_expr e then found := true; e)
      (fun s' -> if lambda_captures_this_stmt s' then found := true; s')
      id_type s);
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
      | e -> map_expr subst_expr subst_stmt id_type e
    and subst_stmt s =
      map_stmt subst_expr subst_stmt id_type s
    in
    let rec walk_expr = function
      | CPPlambda ({cl_capture = Closure; _} as l) ->
        CPPlambda (map_lambda subst_stmt Fun.id l)
      | e -> map_expr walk_expr walk_stmt id_type e
    and walk_stmt s =
      map_stmt walk_expr walk_stmt id_type s
    in
    let self_expr, self_ty =
      if is_value_self then
        (CPPderef CPPthis, Declare self_type)
      else
        (CPPshared_from_this self_type, Declare (Tshared_ptr self_type))
    in
    let self_binding = Sasgn (self_id, self_ty, self_expr) in
    self_binding :: List.map walk_stmt stmts

(** Check if any expression or statement contains [CPPshared_from_this]. *)
let rec expr_has_shared_from_this = function
  | CPPshared_from_this _ -> true
  | CPPlambda {cl_body = body; _} -> List.exists stmt_has_shared_from_this body
  | CPPfun_call (_, f, args) ->
    expr_has_shared_from_this f || List.exists expr_has_shared_from_this (to_reversed args)
  | _ -> false

(** Statement-level counterpart of {!expr_has_shared_from_this}: checks whether
    any statement in a method body contains [CPPshared_from_this]. *)
and stmt_has_shared_from_this = function
  | Sreturn (Some e) -> expr_has_shared_from_this e
  | Sexpr e -> expr_has_shared_from_this e
  | Sif (_, then_stmts, else_stmts) ->
    List.exists stmt_has_shared_from_this then_stmts
    || List.exists stmt_has_shared_from_this else_stmts
  | Scustom_case (_, _, _, brs, _) ->
    List.exists
      (fun (_, _, stmts) -> List.exists stmt_has_shared_from_this stmts)
      brs
  | Sswitch (_, _, brs, default) ->
    List.exists
      (fun (_, stmts) -> List.exists stmt_has_shared_from_this stmts)
      brs
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Smatch (scrut, branches, default) ->
    List.exists
      (fun br -> List.exists stmt_has_shared_from_this br.smb_body)
      branches
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Sasgn (_, _, e) -> expr_has_shared_from_this e
  | _ -> false

(** Generate a single method for an inductive type from a method candidate.
    @param name     [GlobRef] of the containing inductive type
    @param vars     Template type variables of the containing inductive
    @param func_ref Rocq reference for the Rocq function being methodified
    @param body     ML body of the function
    @param ty       ML type of the function
    @param this_pos 0-based index of the [this] argument in the parameter list *)
let gen_single_method name vars (func_ref, body, ty, this_pos) =
  (* Promotion moves a function into a struct; it does not change what the
     function returns.  The mode is read off the codomain here exactly as it is
     for a function left at top level -- otherwise an [itree] body reached as a
     method would be desugared sequentially while the signature it is being
     given says [shared_ptr<ITree<_>>]. *)
  with_itree_mode_for ty @@ fun () ->
  let num_ind_vars = List.length vars in
  let func_name = Common.id_of_global Term func_ref in

  (* Get return type *)
  let all_args, ret_ty = get_args_and_ret [] ty in

  (* Determine the mapping from function type variables to inductive type
     variables. For same-module methods, the function uses Tvars 1..num_ind_vars
     for the inductive. For cross-module methods, the function may use different
     Tvar positions. We extract the actual mapping from the Tglob at this_pos.

     Example: fold_left has type (A → B → A) → list B → A → A where A=Tvar1
     (accumulator), B=Tvar2 (list element). list<B> uses Tvar2, so ind_tvar_map
     = [(2, 1)] meaning "Tvar2 → ind var position 1". Then Tvar1 is "extra" and
     becomes template param T1. *)
  let ind_tvar_map =
    match List.nth_opt all_args this_pos with
    | Some (Miniml.Tglob (_, tvar_args, _)) ->
      (* Extract Tvar indices from the Tglob args, paired with their position.
         Only include entries whose destination position is within the actual
         inductive type vars (1..num_ind_vars).  Type parameters killed during
         extraction (e.g., phantom params) produce Tglob args that map beyond
         the available vars — treat those as extra method tvars instead. *)
      List.filter (fun (_, dst) -> dst <= num_ind_vars)
        (List.concat
          (List.mapi
             (fun pos t ->
               match Table.type_var_of_arg t with
               | Some i -> [(i, pos + 1)]
               | None -> [] )
             tvar_args ))
    | _ ->
      List.init num_ind_vars (fun i -> (i + 1, i + 1))
  in
  let ind_tvar_set = IntSet.of_list (List.map fst ind_tvar_map) in
  (* Remap ML type variables: assign canonical positions so
     convert_ml_type_to_cpp_type maps them correctly. - Inductive tvars →
     positions 1..num_ind_vars - Extra tvars → positions num_ind_vars+1,
     num_ind_vars+2, ... This avoids collisions when the function uses different
     numbering than the inductive.

     Example: fold_left has Tvar1 (accum), Tvar2 (list elem) ind_tvar_map = [(2,
     1)] — Tvar2 is the list element → position 1 extra tvars: [1] — Tvar1 is
     extra → position 2 (= num_ind_vars + 1) Full remap: Tvar1 → 2, Tvar2 → 1 *)
  let all_tvars = List.sort compare (collect_tvars [] ty) in
  let extra_tvars_orig =
    List.filter (fun i -> not (IntSet.mem i ind_tvar_set)) all_tvars
  in
  let needs_remap =
    (not (List.for_all (fun (src, dst) -> src = dst) ind_tvar_map))
    || extra_tvars_orig <> []
  in
  (* Build complete remap table: (original_idx → canonical_idx) *)
  let extra_remap =
    List.mapi (fun i orig -> (orig, num_ind_vars + 1 + i)) extra_tvars_orig
  in
  let full_remap = ind_tvar_map @ extra_remap in
  let remap_ml_tvar i =
    match List.assoc_opt i full_remap with
    | Some canonical -> canonical
    | None -> i
  in
  let rec remap_ml_type = function
    | Miniml.Tvar (rigid, i) -> Miniml.Tvar (rigid, remap_ml_tvar i)
    | Miniml.Tapp (i, args) ->
      Miniml.Tapp (remap_ml_tvar i, List.map remap_ml_type args)
    | Miniml.Tarr (t1, t2) -> Miniml.Tarr (remap_ml_type t1, remap_ml_type t2)
    | Miniml.Tglob (r, args, e) ->
      Miniml.Tglob (r, List.map remap_ml_type args, e)
    | Miniml.Tmeta {contents = Some t} -> remap_ml_type t
    | t -> t
  in
  let _ty = if needs_remap then remap_ml_type ty else ty in
  let ret_ty = if needs_remap then remap_ml_type ret_ty else ret_ty in
  let body =
    if needs_remap then Mlutil.remap_tvars remap_ml_tvar body else body
  in
  (* After remapping, extra tvars are at positions num_ind_vars+1,
     num_ind_vars+2, ... *)
  let extra_tvars = List.map snd extra_remap in
  let extra_tvar_names = List.mapi (fun i _ -> tvar_id (i + 1)) extra_tvars in
  let extra_tvar_map = List.combine extra_tvars extra_tvar_names in
  let subst_extra_tvars = make_subst_extra_tvars num_ind_vars extra_tvar_map in

  (* For type conversion in method contexts, use ns = {name} so that
     self-references INSIDE container types get shared_ptr wrapping
     (matching how struct fields are defined).  Then strip the top-level
     shared_ptr for the method's own type (value-type inductives are
     passed/returned by value, not by shared_ptr). *)
  let method_ns = Refset'.singleton name in
  let rec strip_self_ptr ty =
    match ty with
    | Tshared_ptr (Tglob (g, _, _)) when not (is_enum_inductive g) ->
      (match ty with Tshared_ptr inner -> inner | _ -> ty)
    | Tglob (r, args, es) ->
      Tglob (r, List.map strip_self_ptr args, es)
    | Tfun (args, ret) ->
      Tfun (List.map strip_self_ptr args, strip_self_ptr ret)
    | Tref (k, t) -> Tref (k, strip_self_ptr t)
    | Tconst t -> Tconst (strip_self_ptr t)
    | _ -> ty
  in
  let strip_top_level_self_ptr ty = strip_self_ptr ty in
  let ret_cpp =
    convert_ml_type_to_cpp_type (empty_env ()) ~ns:method_ns
      vars
      ret_ty
  in
  let ret_cpp = strip_top_level_self_ptr ret_cpp in
  let ret_cpp = subst_extra_tvars ret_cpp in

  (* Collect lambda parameters and build environment for de Bruijn lookup.
     push_vars' may rename duplicate parameters (e.g., two params named 't'
     become 't', 't0').

     We must use the renamed ids (all_ids) consistently for: 1. The environment
     - so gen_expr/gen_stmts produce correct variable references 2. The C++
     method signature - so parameter names match what the body references

     Previously, renamed ids were discarded and original names used for the
     signature, causing errors like: void method(tree t) { ... t0->v() ... }
     where 't0' in the body didn't exist as a parameter. *)
  let ids_with_types, inner_body = Mlutil.collect_lams body in
  (* Eta-expansion: if the body has fewer lambdas than the ML type's domain,
     add missing parameters (innermost first, named _x0, _x1, ...).
     This handles functions like [tree_to_adder : tree -> nat -> nat] where
     the body is a match expression returning closures rather than being
     directly lambda-wrapped.  Mirrors the same logic in gen_dfun. *)
  let rec get_method_dom l ty =
    match ty with
    | Tarr (t1, t2) -> get_method_dom (t1 :: l) t2
    | _ -> l
  in
  let mldom_for_eta = get_method_dom [] ty in
  let n_type_dom_eta = List.length mldom_for_eta in
  let n_body_dom_eta = List.length ids_with_types in
  let n_missing_eta = max 0 (n_type_dom_eta - n_body_dom_eta) in
  let ids_with_types, inner_body =
    if n_missing_eta = 0 then (ids_with_types, inner_body)
    else
      let missing_types = safe_firstn n_missing_eta mldom_for_eta in
      let n_miss = List.length missing_types in
      let missing =
        List.mapi
          (fun i t -> (Id (eta_param_id (n_miss - 1 - i)), t))
          missing_types
      in
      let lifted_b = ast_lift n_missing_eta inner_body in
      let args =
        List.rev
          (List.filter_map
             (fun (i, (_, t)) ->
               if isTdummy t then None else Some (MLrel (i + 1)) )
             (List.mapi (fun i x -> (i, x)) missing) )
      in
      (missing @ ids_with_types, apply_eta_args lifted_b args)
  in
  let ids_converted, typeclass_temps =
    promote_typeclass_params
      (List.map (fun (x, ty) -> (cpp_id_of_id (id_of_mlid x), ty)) ids_with_types)
  in
  let all_ids, env = push_vars' ids_converted (empty_env ()) in
  reset_env_types ();
  push_binders env all_ids;
  (* Infer owned/borrowed for method parameters. Note: method 'this' is always
     borrowed (const method). *)
  let n_method_params = List.length ids_with_types in
  let method_owned_flags =
    let base = Escape.infer_owned_params n_method_params inner_body in
    let sub_esc = Escape.infer_sub_bindings_escape_params n_method_params inner_body in
    List.map2 (fun (b, s) (_, ty) ->
      b || (s && is_prod_ml_type ty))
      (List.combine base sub_esc) ids_with_types
  in

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
        (not (ml_type_is_void ty)) && not (Ml_type_util.ml_type_is_instance ty) )
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
  let params_with_idx =
    List.mapi
      (fun i (id, ty, orig_idx) ->
        let cpp_ty =
          convert_ml_type_to_cpp_type env ~ns:method_ns
            vars
            ty
        in
        let cpp_ty = strip_top_level_self_ptr cpp_ty in
        let cpp_ty = subst_extra_tvars cpp_ty in
        let owned = get_param_owned_flag orig_idx in
        (id, cpp_ty, i, owned) )
      param_ids_with_pos
  in

  (* Extract function-typed parameters for template params *)
  let fun_params =
    List.filter_map
      (fun (id, cpp_ty, i, _) ->
        match cpp_ty with
        | Tfun (dom, cod) ->
          let cod = if is_cpp_unit_type cod then Tvoid else cod in
          Some (id, TTfun (dom, cod), fun_tparam_id i)
        | _ -> None )
      params_with_idx
  in

  (* Build template params *)
  let extra_type_params =
    List.map (fun name -> (TTtypename, name)) extra_tvar_names
  in
  let fun_template_params =
    List.map (fun (_, tt, fname) -> (tt, fname)) fun_params
  in
  (* The instances come first, as they do for a free function: a call site
     spells the same list in the same order. *)
  let template_params =
    List.map (fun (tt, id, _, _) -> (tt, id)) typeclass_temps
    @ extra_type_params
    @ fun_template_params
  in

  (* Build final params with proper wrapping. Use escape analysis to determine
     owned vs borrowed: owned params are passed by value (for move semantics),
     borrowed params are passed by const ref. This matches gen_dfun's logic to
     ensure forward declarations and definitions agree. *)
  let params =
    List.map
      (fun (id, cpp_ty, i, owned) ->
        let wrapped =
          match cpp_ty with
          | Tfun _ -> Tref (Forwarding, named_tvar (fun_tparam_id i))
          | _ -> wrap_param_by_ownership ~is_owned:owned cpp_ty
        in
        (id, wrapped) )
      params_with_idx
  in

  (* Suspended at its constructors, and whole only where it calls itself
     outside all of them: see [cofix_wrap] in [gen_dfun]. *)
  let is_cofix_method =
    Table.is_coinductive_type ret_ty
    && calls_eagerly func_ref (snd (collect_lams body))
  in
  let method_k x =
    if is_cofix_method then
      let type_args =
        match ret_ty with
        | Miniml.Tglob (_, args, _) ->
          List.map
            (fun t ->
              convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
                vars
                t )
            args
        | _ -> []
      in
      let coind_ref =
        match ret_ty with
        | Miniml.Tglob (r, _, _) -> r
        | _ ->
          CErrors.anomaly
            (Pp.str
               "gen_method_field: cofixpoint return type expected to be Tglob" )
      in
      let lazy_factory =
        CPPscope (mk_cppglob coind_ref type_args, Id.of_string "lazy_", [])
      in
      let thunk = mk_lambda [] (Some ret_cpp) [Sreturn (Some x)] ~capture:Closure in
      Sreturn (Some (mk_call lazy_factory [thunk]))
    else
      Sreturn (Some x)
  in
  (* Generate method body. Initialize move tracking for owned parameters.
     'this' is always borrowed (const method). *)
  let saved_dead = (!tctx).move_dead_after in
  let saved_owned = (!tctx).move_owned_vars in
  let saved_nparams = (!tctx).move_n_params in
  begin_body ();
  (* Initialize owned-variable tracking for method parameters.
     The de Bruijn environment has parameters in reverse order:
     ids_normal_order has outermost-first, push_vars' reverses them. *)
  let method_n_params = List.length ids_with_types in
  tctx := { !tctx with move_n_params = method_n_params };
  (* method_owned_flags[i] corresponds to de Bruijn index i+1.
     db index i+1 maps to ids_with_types[i] (outermost-first, same order
     as push_vars' which prepends in list order).
     Only track ownership for non-trivial types (inductives). *)
  tctx :=
    { !tctx with
      move_owned_vars =
          List.fold_left
            (fun acc (i, owned) ->
              (* Under [Crane Reuse], the receiver at [this_pos] is a const [this]
                 (borrowed) and must never be treated as owned, or a reuse arm would
                 try to consume it via v_mut() on a const method.  Gated on reuse so
                 reuse-off output stays byte-identical to the pre-reuse baseline. *)
              if owned && not (Table.reuse () && Table.reuse_loopify_ok () && i = this_pos)
              then
                let ml_ty = snd (List.nth ids_with_types i) in
                if Escape.is_shared_ptr_type ml_ty
                   || is_nontrivial_value_ml_type ml_ty then
                  Escape.IntSet.add (i + 1) acc
                else acc
              else acc )
            Escape.IntSet.empty
            (List.mapi (fun i o -> (i, o)) method_owned_flags) };
  (* The scope covers both the inductive's type vars and the extra ones, so
     that gen_expr/eta_fun convert Tvars to the named C++ types the method
     body expects (e.g. recursive calls carry type args). *)
  let stmts =
    with_type_vars (vars @ extra_tvar_names) (fun () ->
        (* Include all local value-type inductives with recursive fields in the
           method ns.  This ensures that when the method body constructs or
           manipulates containers of recursive types (e.g. List<tree>), the
           type arguments get shared_ptr wrapping to match struct field
           types. *)
        with_method_ns_for_locals ~base:method_ns (fun () ->
            gen_stmts env method_k inner_body ) )
  in
  tctx := { !tctx with move_dead_after = saved_dead };
  tctx := { !tctx with move_owned_vars = saved_owned };
  tctx := { !tctx with move_n_params = saved_nparams };
  (* Add type args to recursive self-calls. Inside fixpoint bodies, the
     extraction produces MLglob(func_ref, []) with empty type args for recursive
     references. When the function is a method, the recursive call needs
     explicit template args for non-deducible params. Replace CPPglob(func_ref,
     []) with CPPglob(func_ref, all_type_args).

     The type args must be in the ORIGINAL tys order (matching
     ind_tvar_positions used by pp_cpp_expr for filtering). Position i in tys
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
  (* Compute self_type unconditionally — needed by both return-this and
     lambda-this passes. *)
  let self_type_args =
    List.map named_tvar vars
  in
  let self_type = Tglob (name, self_type_args, []) in
  let stmts =
    if contains_shared_ptr ret_cpp then
      List.map (replace_return_this_stmt self_type) stmts
    else stmts
  in
  (* Replace [CPPthis] with [CPPshared_from_this] inside by-value lambda
     bodies.  When a method returns a closure that captures [this], the raw
     pointer would dangle after the caller's [shared_ptr] is released.
     Using [shared_from_this()] inside the lambda ensures the closure keeps
     the object alive. *)
  let stmts = return_captures_by_value stmts in
  let stmts = replace_this_in_lambdas self_type stmts in
  (* Apply tvar_subst_stmt with the extended vars list (defined above).
     extended_vars covers positions 1..num_ind_vars (inductive vars) and
     num_ind_vars+1, num_ind_vars+2, etc. (extra vars) so tvar_subst_stmt can
     name them all correctly. *)
  let stmts = List.map (tvar_subst_stmt extended_vars) stmts in

  let no_pure = is_monadic_ml_type ret_ty in
  (* Filter out phantom extra template params: if an extra tvar name doesn't
     appear in any param type or the return type, it's phantom (e.g., a killed
     inductive type arg) and shouldn't be a template param. *)
  (* Whether a type mentions the template parameter [name] anywhere. *)
  let cpp_type_has_tvar name =
    exists_cpp_type (function
      | Tvar (Tv_index (_, Some n) | Tv_named n) -> Id.equal n name
      | _ -> false )
  in
  let extra_tvar_name_set =
    List.fold_left (fun s n -> Id.Set.add n s) Id.Set.empty extra_tvar_names
  in
  (* The body counts too.  A tvar the signature never mentions is usually one
     erasure killed outright, but a local binding can still be declared at it
     -- the result of a trigger is an index of the event type, so it has no
     spelling but the variable's own -- and dropping the parameter leaves the
     body naming something that is no longer declared. *)
  let stmt_has_tvar name stmts =
    let found = ref false in
    let rec on_type t =
      if cpp_type_has_tvar name t then found := true;
      t
    and on_expr e = Minicpp.map_expr on_expr on_stmt on_type e
    and on_stmt s = Minicpp.map_stmt on_expr on_stmt on_type s in
    List.iter (fun s -> ignore (on_stmt s)) stmts;
    !found
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
          && cpp_type_has_tvar tname ret_cpp
          && (not (List.exists (fun (_, pty) -> cpp_type_has_tvar tname pty) params))
          && not (stmt_has_tvar tname stmts)
        then Some tname
        else None )
      template_params
  in
  let return_only_set =
    List.fold_left (fun s n -> Id.Set.add n s) Id.Set.empty return_only_tvars
  in
  let ret_cpp, stmts =
    if Id.Set.is_empty return_only_set then (ret_cpp, stmts)
    else
      let erased =
        map_cpp_type
          (function
            | Tvar (Tv_index (_, Some n) | Tv_named n) when Id.Set.mem n return_only_set -> Tany
            | t -> t )
          ret_cpp
      in
      (* The body still builds its value at the one type it knows; the
         signature now promises the erased one.  [crane_container_cast] is the
         conversion between the two, and it is the identity when they agree.

         A return type that erased away entirely needs nothing said: anything
         converts to [std::any] by boxing. *)
      let rec cast_stmt s =
        match s with
        | Sreturn (Some e) -> Sreturn (Some (CPPcontainer_cast (erased, e, false)))
        | _ -> Minicpp.map_stmt (fun e -> e) cast_stmt (fun t -> t) s
      in
      if erased = Tany then (erased, stmts) else (erased, List.map cast_stmt stmts)
  in
  let template_params =
    List.filter (fun (_tt, tname) ->
      if not (Id.Set.mem tname extra_tvar_name_set) then true
      else if Id.Set.mem tname return_only_set then false
      else
        cpp_type_has_tvar tname ret_cpp
        || List.exists (fun (_, pty) -> cpp_type_has_tvar tname pty) params
        || stmt_has_tvar tname stmts)
    template_params
  in
  let surviving_names =
    List.fold_left (fun s (_, n) -> Id.Set.add n s) Id.Set.empty template_params
  in
  let phantom_positions =
    List.filter_map (fun (orig_idx, name) ->
      if Id.Set.mem name extra_tvar_name_set
         && not (Id.Set.mem name surviving_names) then
        Some (orig_idx - 1)
      else None)
      (List.combine extra_tvars_orig extra_tvar_names)
  in
  if phantom_positions <> [] then
    Table.set_phantom_tvars func_ref phantom_positions;
  let phantom_name_set =
    List.fold_left (fun s (_, n) -> Id.Set.add n s) Id.Set.empty
      (List.filter (fun (_, n) ->
        Id.Set.mem n extra_tvar_name_set && not (Id.Set.mem n surviving_names))
        (List.combine extra_tvars_orig extra_tvar_names))
  in
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
  (* The parameter types are decided here; the printer needs them when the
     method is later passed around as a function value and has to be spelled as
     a forwarding lambda. *)
  Cpp_state.register_method_param_cpp_types func_ref (List.map snd params);
  ( Fmethod
      {
        mf_name = func_name;
        mf_globref = Some func_ref;
        mf_tparams = template_params;
        mf_ret_type = ret_cpp;
        mf_params = params;
        mf_body = stmts;
        mf_receiver = Instance { this_pos = this_pos; is_const = true; ref_qual = Rq_any };
        mf_is_inline = false;
        mf_no_pure = no_pure;
        mf_is_noexcept = false;
        mf_is_conversion = false;
      },
    VPublic,
    SNoTag )

(** Generate C++ header for an inductive type (v2 style: encapsulated struct
    with methods).

    Produces a self-contained struct with:
    - Nested constructor-alternative structs (e.g. [Leaf {}], [Node { ... }])
    - [using variant_t = std::variant<Leaf, Node>]
    - Private [variant_t d_v_] data member
    - Explicit constructors for each alternative
    - Static factory methods ([cons(...)], [cons_uptr(...)]) with move semantics
    - Methods from [method_candidates] (with [this] substitution)

    @param consarg_names  binder names from {!Miniml.ml_ind_packet.ip_consarg_names};
      when provided, constructor struct fields and factory parameters use
      descriptive names derived from the Rocq source instead of [d_a0] etc. *)

(** Does the ML type [ml_ty] contain [ind_ref] (or a mutual sibling) anywhere
    in its type arguments — but NOT at the top level?  Used to detect fields
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

(** Completeness-aware element wrapping (WRAP.md): if a constructor field of
    [ind_ref] recurses THROUGH a boxed-element container (a container carrying a
    [Boxed Element] wrapper, e.g. [list <self>] where [list -> immer::flex_vector]),
    record [ind_ref] as an inductive that must be boxed as a container element
    everywhere it occurs, so its C++ representation is type-consistent. Call this
    for every constructor field type. *)
let maybe_record_boxed_recursive_ind ~ind_ref ml_ty =
  if ml_type_recurses_through_boxed_container ~ind_ref ml_ty then
    Table.add_boxed_recursive_ind ind_ref

(** Generate the C++ struct definition for an inductive type.

    Produces one of three shapes depending on the inductive:
    - {b Value type}: a struct with an inner [std::variant] of constructor
      structs, factory methods, and [v()]/[v_mut()] accessors.
    - {b Shared-ptr type}: same struct wrapped in [std::shared_ptr] at use
      sites, with [shared_from_this] support and pointer-based destructors.
    - {b Enum}: a simple [enum class] with no variant or constructor structs.

    Major sections generated (in order): constructor structs, variant typedef,
    factory methods, iterative destructor (for recursive types),
    converting constructor (for mutual-inductive field-type differences),
    [operator==], and stream insertion.

    @param is_mutual     true when this type is part of a mutual block
    @param consarg_names field names from Rocq binders, indexed by constructor
    @param mutual_partners other types in the mutual block *)

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
  let is_coinductive = ind_kind = Coinductive in
  (* Scoped-arena redesign (2026-08-10): arena allocation is no longer a
     compile-time property of the type.  Every recursive field is the ordinary
     smart pointer ([std::shared_ptr] / [crane::rc]); the recursive-field factory
     is the *runtime-arena-aware* one ([crane::arena_make_shared] /
     [crane::rc<T>::make], see [Alloc_arena_scoped]), which bump-allocates from the
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
  let ty_vars = List.map named_tvar vars in

  (* Handle empty inductives (no constructors) - generate uninhabitable
     struct *)
  if Array.length cnames = 0 then
    (* For empty types like `Inductive empty : Type := .`, generate: struct
       empty { empty() = delete; }; This type cannot be constructed, matching
       the semantics of empty types. *)
    let method_fields =
      List.map (gen_single_method name vars) method_candidates
    in
    Dstruct
      {
        ds_ref = name;
        ds_fields = [(Fdeleted_ctor, VPublic, SNoTag)] @ method_fields;
        ds_tparams = templates;
        ds_constraint = None;
        ds_needs_shared_from_this = false;
      }
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
                 Id.of_string (Table.enum_ctor_name_of_ref kn i cidx)
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
      Denum
        {
          de_ref = name;
          de_ctors = ctor_names;
          de_ctor_rocq_names = rocq_names;
          de_tparams = [];
        } )
    else
      (* The main struct type: all inductives (including coinductives)
         are value types. *)
      let self_ty = Tglob (name, ty_vars, []) in
      let ind_type_name_str = Common.pp_global_name Type name in

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
        let flat_fields =
          List.mapi (fun j ty ->
            let cpp_ty =
              erase_if_needed
                (convert_ml_type_to_cpp_type (empty_env ()) vars ty) in
            let field_id = List.nth field_ids j in
            (Fvar (field_id, cpp_ty), VPublic, SData)
          ) tys_list
        in
        let field_exprs = List.map (fun fid -> CPPvar fid) field_ids in
        let clone_body = [Sreturn (Some (CPPbraced field_exprs))] in
        let clone_field =
          ( Fmethod
              { mf_name = Id.of_string "clone";
                mf_globref = None;
                mf_tparams = [];
                mf_ret_type = self_ty;
                mf_params = [];
                mf_body = clone_body;
                mf_receiver = Instance { this_pos = 0; is_const = true; ref_qual = Rq_any };
                mf_is_inline = false;
                mf_no_pure = true;
                mf_is_noexcept = false;
                mf_is_conversion = false },
            VPublic, SAccessors )
        in
        let conversion_field =
          (* An inductive's [vars] already begin with its promoted variables
             (see [Cpp_ind]), so nothing is left to keep. *)
          conversion_to_other_instantiation ~leading:[] ~name ~templates ~vars
            ~fields:
              (List.mapi
                 (fun j ty ->
                   ( List.nth field_ids j,
                     fun var_names ->
                       erase_if_needed
                         (convert_ml_type_to_cpp_type (empty_env ()) var_names
                            ty) ) )
                 tys_list)
        in
        let factory_name =
          Id.of_string (factory_name_of_ctor ~type_name:ind_type_name_str cname_str)
        in
        let factory_params =
          List.mapi (fun j ty ->
            let cpp_ty =
              erase_if_needed
                (convert_ml_type_to_cpp_type (empty_env ()) vars ty) in
            let fid = List.nth field_ids j in
            (fid, cpp_ty)
          ) tys_list
        in
        let factory_args =
          List.map (fun (param_name, cpp_ty) ->
            if is_trivially_copyable_type cpp_ty then CPPvar param_name
            else CPPmove (CPPvar param_name)
          ) factory_params
        in
        let factory_body = [Sreturn (Some (CPPbraced factory_args))] in
        let factory_field =
          ( Fmethod
              (static_fun ~name:factory_name ~ret:self_ty
                 ~params:factory_params ~body:factory_body),
            VPublic, SCreators )
        in
        let method_fields = List.map (gen_single_method name vars) method_candidates in
        let all_flat_fields =
          flat_fields @ [clone_field] @ conversion_field @ [factory_field]
          @ method_fields
        in
        Dstruct
          { ds_ref = name;
            ds_fields = all_flat_fields;
            ds_tparams = templates;
            ds_constraint = None;
            ds_needs_shared_from_this = false; }
      end else

      let _ = ind_type_name_str in (* suppress unused warning if non-flat path also needs it *)

      (* Compute a field's final C++ type, including the arena-mode
         pointerization of recursive fields.  Used for the per-constructor
         nested struct field declarations below. (The old arena deep-copy
         constructor that also consumed this was removed in the scoped-arena
         redesign; see the note near [value_copy_clone_methods].) *)
      let compute_field_cpp_ty ty =
        let cpp_ty =
          convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
            vars
            ty
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
        (* Completeness-aware element wrapping (WRAP.md). *)
        maybe_record_boxed_recursive_ind ~ind_ref:name ty;
        let cpp_ty =
          if ml_type_has_nested_self_ref ~ind_ref:name ty && not is_coinductive
          then
            let bare_cpp_ty =
              convert_ml_type_to_cpp_type
                (empty_env ())
                vars
                ty
            in
            (* If the field recurses THROUGH a boxed-element
               container, the element box already breaks the
               completeness cycle, so the outer shared_ptr/arena
               pointer is redundant: store the container by value. *)
            if (not is_coinductive)
               && ml_type_recurses_through_boxed_container
                    ~ind_ref:name ty
            then bare_cpp_ty
            else Tshared_ptr bare_cpp_ty
          else cpp_ty
        in
        let cpp_ty =
          if vars = [] then
            match cpp_ty with
            | Tshared_ptr _ ->
              tvar_erase_type cpp_ty
            | _ when has_unnamed_tvar cpp_ty -> Tany
            | _ -> cpp_ty
          else cpp_ty
        in
        (* Scoped-arena redesign: recursive fields are always the ordinary
           smart pointer ([Tshared_ptr], rendered as std::shared_ptr /
           crane::rc); arena-ness is decided per-object at the factory call
           site, not baked into the field type. *)
        cpp_ty
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
                ( Id.of_string ("_S" ^ string_of_int k),
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
        { dfs_name = cname;
          dfs_selves = List.map snd selves;
          dfs_fields = List.map (fun (f, ty) -> (f, through_selves ty)) fields }
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
               let deferred = deferred_ctor_struct cname fields in
               if is_coinductive && deferred.dfs_fields <> fields then
                 (Fdeferred_struct deferred, VPublic, STypes)
               else
                 ( Fnested_struct
                     ( cname,
                       List.map (fun (f, ty) -> (Fvar (f, ty), VPublic, SNoTag)) fields ),
                   VPublic,
                   STypes ) )
             tys )
      in

      (* 2. variant_t type alias - use simple Id-based refs that match nested struct names *)
      (* Note: nested structs inherit template params from parent, so don't add <A> to them *)
      let variant_ty =
        Tvariant
          (Array.to_list
             (Array.mapi
                (fun i c ->
                  let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                  (* Use Tid for local nested struct types - no template args
                     since they inherit *)
                  Tid (cname_id, []) )
                cnames ) )
      in
      (* Collision detection: internal names must not equal the enclosing type name *)
      let type_name_str = Common.pp_global_name Type name in
      let escape_if_clashes base =
        if String.equal base type_name_str then base ^ "_" else base
      in
      let variant_alias_name = escape_if_clashes "variant_t" in
      let variant_using =
        (Fnested_using ([], Id.of_string variant_alias_name, variant_ty), VPublic, STypes)
      in
      (* A type parameterised by families is itself one: [crane::rebind_t]
         leaves it alone, as the family's own struct it is, rather than
         reading its erased index as an element (see [obj.h]). *)
      let element_using =
        if List.exists (fun i -> Table.is_family_ind_param name i)
             (List.init (List.length vars) Fun.id)
        then
          [ ( Fnested_using ([], Id.of_string "crane_family_tag", Tvoid),
              VPublic,
              STypes ) ]
        else []
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
      let variant_alias_ty = Tid (variant_alias_id, []) in
      let vmn_id = Id.of_string variant_member_name in
      let variant_member_ty =
        if is_coinductive then
          Tid_external (Crane_rt.lazy_, [variant_alias_ty])
        else
          variant_alias_ty
      in
      let variant_member =
        ( Fvar (Id.of_string variant_member_name, variant_member_ty),
          VPrivate,
          SData )
      in

      (* A coinductive's cell type, [crane::lazy<variant_t>], as the callee of
         its constructor. *)
      let lazy_cell =
        CPPvar (Id.of_string_soft (Crane_rt.lazy_ ^ "<" ^ variant_alias_name ^ ">"))
      in

      (* 4. Public explicit constructors for each alternative.
         Public so that std::make_shared / std::make_unique can construct
         instances directly (single allocation). *)
      (* Note: nested struct types don't need template args - they inherit from parent *)
      let public_ctors =
        Array.to_list
          (Array.mapi
             (fun i c ->
               let cname = ctor_struct_id_of_ref ~fallback_idx:i c in
               let param_name = Id.of_string "_v" in
               let param_ty = Tid (cname, []) in
               if is_coinductive then
                 (* For coinductive:
                    d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) *)
                 let init_expr =
                   mk_call lazy_cell
                     [ mk_call (CPPvar variant_alias_id)
                         [CPPmove (CPPvar param_name)] ]
                 in
                 let init_list = [(vmn_id, init_expr)] in
                 ( Fconstructor
                     { fc_tparams = [];
                       fc_params = [(param_name, param_ty)];
                       fc_inits = init_list;
                       fc_body = [];
                       fc_explicit = true;
                       fc_noexcept = false },
                   VPublic,
                   SCreators )
               else
                 (* For inductive: d_v_(std::move(_v)) when the constructor
                    struct has non-trivial fields (shared_ptr etc.).  For
                    trivially-copyable structs (e.g., empty nullary constructors
                    like O, Nil, Leaf), skip std::move — it has no effect and
                    triggers performance-move-const-arg. *)
                 let has_nontrivial_fields =
                   List.exists (fun ty -> not (isTdummy ty)) tys.(i)
                 in
                 let init_v =
                   if has_nontrivial_fields then CPPmove (CPPvar param_name)
                   else CPPvar param_name
                 in
                 let init_list =
                   [(vmn_id, init_v)]
                 in
                 ( Fconstructor
                     { fc_tparams = [];
                       fc_params = [(param_name, param_ty)];
                       fc_inits = init_list;
                       fc_body = [];
                       fc_explicit = true;
                       fc_noexcept = false },
                   VPublic,
                   SCreators ) )
             cnames )
      in

      (* Default constructor, which lets loopify declare [T _result{};] for
         stack-based iteration.  An inductive's variant default-constructs to
         its first alternative (e.g. Nil); a coinductive's lazy cell to an
         empty one -- the state a moved-from value is already in, and which
         only a slot written before it is read, as [_result] is, may hold. *)
      let default_ctor =
        [( Fconstructor
            { fc_tparams = [];
              fc_params = [];
              fc_inits = [];
              fc_body = [];
              fc_explicit = false;
              fc_noexcept = false },
           VPublic,
           SCreators )]
      in

      (* Iterative destructor preventing stack overflow from deeply recursive
         [shared_ptr] chains.  Drains recursive fields into an explicit stack,
         only entering nodes with [use_count() == 1] (sole ownership).

         Self-recursive types use [shared_ptr<Self>] directly on the stack.
         Mutually recursive types use [std::any] to hold different [shared_ptr]
         types.  Returns [[]] for non-recursive or coinductive types. *)
      let iterative_destructor =
        (* Scoped-arena redesign: recursive fields are ordinary smart pointers
           even for arena-backed values (the region only owns the payload
           memory; per-node refcounting still drives destruction), so the
           iterative destructor that drains those smart-pointer chains is
           needed here exactly as for any other recursive type. *)
        if is_coinductive then []
        else
          (* Check whether ML type [t] is a reference to [ref_name] applied to
             the same type variables [ref_vars] (i.e., a direct recursive or
             mutual recursive occurrence). *)
          let rec is_ref_to ref_name ref_vars = function
            | Miniml.Tglob (r, args, _) ->
              globref_equal r ref_name
              && List.length args = List.length ref_vars
              && List.for_all
                   (fun (j, arg) ->
                     match arg with
                     | Miniml.Tvar (_, k) -> k = j + 1
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar (Schematic, k))}
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar (Rigid, k))} ->
                       k = j + 1
                     | _ -> false)
                   (List.mapi (fun j a -> (j, a)) args)
            | Miniml.Tmeta {contents = Some t} -> is_ref_to ref_name ref_vars t
            | _ -> false
          in
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
             list, so without this the type looked non-recursive, no drain
             was emitted at all, and destruction recursed once per level
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

             [is_list_global] matches only the stdlib [list], by name.  A
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
                    a user-defined option-like inductive, ...  The three cases
                    above cover only the shapes that predate the general
                    harvester; everything else is handed to [harvest_field],
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
          let self_ty = Tglob (name, ty_vars, []) in
          (* Qualify inductive references for use outside [name]'s own scope;
             [name] itself is skipped because the destructor is written inside
             it. *)
          let q_destr ty =
            let skip g = GlobRef.CanOrd.equal g name in
            qualify_inductives ~skip ty
          in
          (* Expand a [Drain "..."] template for a custom container field into a
             statement list. [%scrut] -> the container field expression [scrut];
             [%yield(e)] -> a structured [push_back(make_rc<Self>(e))] onto the
             worklist. The template is split into raw chunks around the structured
             pushes so that the [_stack] reference is a real [CPPvar] the lambda
             capture-analysis can see (a fully-raw body would collapse to an
             empty [[]] capture). [%yield]'s argument is captured with
             balanced-paren matching, so it may itself contain parentheses
             (e.g. [std::move(%scrut.front())]). *)
          let expand_drain_template ~scrut ~self tmpl =
            let subst s = Common.render_template [("%scrut", scrut)] s in
            List.map
              (function
                | Foreign_template.Drain_text t -> Sraw (subst t)
                | Drain_yield arg ->
                  Sexpr
                    (CPPaccess_call
                       ( Adot,
                         CPPvar _stack_id,
                         Id.of_string "push_back",
                         [mk_call (CPPalloc (Alloc_heap, self)) [CPPraw (subst arg)]] )) )
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
             no atomics, no decrement to pair with -- so no fence is emitted
             and <atomic> is not included (see extract_env.ml). *)
          let unique_fence =
            if Table.non_atomic_rc () then []
            else (
              Common.require_header "atomic";
              [Sraw "std::atomic_thread_fence(std::memory_order_acquire);"] )
          in
          let is_sole p =
            CPPbinop (Beq, CPPaccess_call (Adot, p, Id.of_string "use_count", []), CPPint 1)
          in
          (* ---------------------------------------------------------------
             Generic mediator harvester.

             A constructor field whose type merely *contains* [Self] --
             [(Self * nat)], [option (option Self)], [list (nat * Self)],
             [cell Self], [w Self] where [w] holds a [list] -- reaches its
             nested [Self]s through an arbitrary composition of products,
             options, records and other inductives.  Each such shape used to
             need its own case in [classify_ml_self_ref]; anything unrecognised
             got no drain at all, so destroying a deep value recursed once per
             level and overflowed the stack (CWE-674).

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
             [Harvest_bail] and the field is left undrained -- the previous
             behaviour, never something worse. *)
          let harvest_fuel = 12 in
          let hv_seq = ref 0 in
          let fresh_hv p =
            incr hv_seq;
            p ^ string_of_int !hv_seq
          in
          let cpp_of_ml t =
            convert_ml_type_to_cpp_type (empty_env ()) vars t
          in
          (* Spelled as from outside the inductive's own scope, which is where
             the destructor's helper types are named. *)
          let outer_ty = q_destr in
          let outer_ml t = outer_ty (cpp_of_ml t) in
          (* [e.m()] -- the harvester only ever calls nullary members
             ([use_count], [reset], [has_value], [v_mut]) on a value. *)
          let dot0 e m = CPPaccess_call (Adot, e, Id.of_string m, []) in
          (* [p->m()], for a [p] that is a raw or smart pointer. *)
          let arrow0 e m = CPPaccess_call (Aarrow, e, Id.of_string m, []) in
          (* Guard [body] on [p] being the sole owner of its pointee -- every
             drain moves a value out of one, so it must first establish that
             nobody else can see it.  The acquire fence follows the [use_count]
             test rather than preceding it; see {!unique_fence}. *)
          let sole_owner p body =
            [Sif (
              CPPbinop (Band, p,
                CPPbinop (Beq, dot0 p "use_count", CPPint 1)),
              unique_fence @ body, [])]
          in
          (* [_stack.push_back(make_shared<Self>(std::move(e)))] -- hand one
             discovered [Self] to the destructor's worklist. *)
          let push_self_stmt e =
            Sexpr (CPPaccess_call (Adot, 
              CPPvar _stack_id,
              Id.of_string "push_back",
              [ mk_call
                  (CPPalloc (Alloc_heap, outer_ty self_ty))
                  [CPPmove e] ]))
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
                      let body = harvest_val (fuel - 1) a (CPPderef e) in
                      if body = [] then []
                      else [Sif (dot0 e "has_value", body, [])]
                    | _ -> raise Harvest_bail)
                 | Some tmpl when starts_with "std::pair" tmpl ->
                   (match args with
                    | [a; b] ->
                      let fld n = CPPaccess (Adot, e, Id.of_string n) in
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
            let body = harvest_val fuel ty (CPPderef p) in
            if body = [] then []
            else sole_owner p (body @ [Sexpr (dot0 p "reset")])
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
                       else
                         let fe =
                           access
                             (Common.lookup_ctor_field_name ~owner:g cname_str k)
                         in
                         let is_ptr = field_is_ptr g fty in
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
                           CPPaccess
                             (Adot, x, Id.of_string_soft (List.nth names k))
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
                field_stmts cname_str (fun f -> CPPaccess (Adot, x, f)) ftys
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
                        CPPaccess (Aarrow, CPPvar av, f) )
                        ftys
                    in
                    if inner = [] then []
                    else
                      [Sif_decl (
                         av, Tptr Tauto,
                         CPPstd_get_if (
                           Tqualified (g_cpp, Id.of_string_soft cname_str),
                           CPPunop (Uaddr, dot0 x "v_mut")),
                         inner, [])])
                  ctors
            in
            if not self_recursive then body_for None e
            else begin
              Table.mark_needs_small_vector ();
              let wl = fresh_hv "_hw" in
              let wl_id = Id.of_string wl in
              let pv = Id.of_string (wl ^ "p")
              and ev = Id.of_string (wl ^ "e") in
              let wl_ty =
                Tid_external
                  (Crane_rt.small_vector, [Tshared_ptr (outer_ml g_ty)])
              in
              let push fe =
                [Sexpr (CPPaccess_call (Adot, 
                   CPPvar wl_id, Id.of_string "push_back", [CPPmove fe]))]
              in
              let on_spine = Some push in
              [Sdecl (wl_id, wl_ty)]
              @ body_for on_spine e
              @ [Swhile (
                   CPPunop (Unot, dot0 (CPPvar wl_id) "empty"),
                   [ Sasgn (pv, Declare Tauto,
                       CPPmove (dot0 (CPPvar wl_id) "back"));
                     Sexpr (dot0 (CPPvar wl_id) "pop_back");
                     Sif (
                       CPPbinop (Bor, CPPunop (Unot, CPPvar pv),
                         CPPbinop (Bneq, dot0 (CPPvar pv) "use_count",
                           CPPint 1)),
                       [Scontinue], []) ]
                   @ unique_fence
                   @ [Sasgn (ev, Declare (Tref (Lvalue, Tauto)), CPPderef (CPPvar pv))]
                   @ body_for on_spine (CPPvar ev))]
            end
          in
          (* Drain statements for a nested-mediator field, or [None] if the
             shape is one the harvester does not handle. *)
          let harvest_field field_id ml_ty =
            try
              let fe = CPPaccess (Aarrow, CPPvar _alt_id, field_id) in
              match harvest_ptr harvest_fuel ml_ty fe with
              | [] -> None
              | stmts -> Some stmts
            with Harvest_bail | Not_found -> None
          in
          (* Build drain statements for classified fields.  [Direct] fields get
             a simple [push_back(std::move(field))].  [List g] fields with a
             custom mapping (e.g. std::deque) iterate elements onto the stack. *)
          let mk_classified_field_stmts classified_fields =
            List.concat_map (fun (field_id, cls) ->
              let fe = CPPaccess (Aarrow, CPPvar _alt_id, field_id) in
              match cls with
              | `Stmts stmts -> stmts
              | `Direct ->
                (* Only a child this node owns alone would be freed with it;
                   any other is a decrement, done by the member's own
                   destructor, and never touches the worklist. *)
                [Sif (CPPbinop (Band, fe, is_sole fe),
                  [Sexpr (CPPaccess_call (Adot, 
                     CPPvar _stack_id,
                     Id.of_string "push_back",
                     [CPPmove fe]))], [])]
              | `Wrapper wfields ->
                (* Reach through a uniquely-owned wrapper cell and move each
                   nested [Self] onto the worklist, then drop the cell. *)
                sole_owner fe
                  (List.map
                     (fun wf -> push_self_stmt (CPPaccess (Aarrow, fe, wf)))
                     wfields
                   @ [Sexpr (dot0 fe "reset")])
              | `List list_g ->
                (* This iterative drain replaces the naive recursive destructor,
                   so cleanup of a deep deque-backed recursive value no longer
                   overflows the call stack (the primary CWE-674 mitigation;
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
                      [ Sfor_range (elem, CPPderef fe,
                          [push_self_stmt (CPPvar elem)]);
                        Sexpr (dot0 fe "reset") ]
                  end
                else
                  let ls = outer_ty (Tglob (list_g, [self_ty], [])) in
                  let (_nil_s, cons_s) = list_ctor_struct_names list_g in
                  let cons_id = Id.of_string_soft cons_s in
                  let elem_field =
                    Common.lookup_ctor_field_name ~owner:list_g cons_s 0
                  in
                  let tail_field =
                    Common.lookup_ctor_field_name ~owner:list_g cons_s 1
                  in
                  let lp = Id.of_string "_lp" and lc = Id.of_string "_lc" in
                  let tail = CPPaccess (Adot, CPPvar lc, tail_field) in
                  (* Walk the cons spine, moving each element onto the
                     worklist.  Ownership must be re-established at every cell,
                     not just the head: list cells share their tails through
                     [shared_ptr], so a suffix reachable from here may still be
                     owned by a live value.  Moving out of such a cell would gut
                     a list someone else is holding, so stop the walk as soon as
                     a tail is not uniquely owned -- the remaining cells then
                     die with their real owner. *)
                  sole_owner fe
                    [ Sasgn (lp, Declare Tauto, dot0 fe "get");
                      Swhile (
                        mk_call
                          (CPPstd_holds_alternative (Tqualified (ls, cons_id)))
                          [arrow0 (CPPvar lp) "v"],
                        [ Sasgn (lc, Declare (Tref (Lvalue, Tauto)),
                            CPPstd_get (Tqualified (ls, cons_id),
                              Some (arrow0 (CPPvar lp) "v_mut")));
                          push_self_stmt
                            (CPPaccess (Adot, CPPvar lc, elem_field));
                          Sif (
                            CPPbinop (Band, tail,
                              CPPbinop (Beq, dot0 tail "use_count", CPPint 1)),
                            (* The fence follows the [use_count] test rather
                               than preceding it -- see [unique_fence]. *)
                            unique_fence
                            @ [Sasgn (lp, Existing, dot0 tail "get")],
                            [Sbreak]) ]);
                      Sexpr (dot0 fe "reset") ]
              | _ -> []) classified_fields
          in
          (* For each constructor, classify recursive fields and build an
             [Sif_decl] that uses [get_if] to test the variant alternative
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
                | None -> Tid (ctor_id, [])
                | Some _ -> Tqualified (parent_ty, ctor_id)
              in
              Some (Sif_decl (
                _alt_id, Tptr Tauto,
                CPPstd_get_if (ctor_arg,
                  CPPunop (Uaddr, CPPvar variant_var)),
                mk_classified_field_stmts classified_fields,
                []))
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
            let ptr_ty = Tshared_ptr self_ty in
            let next_id = Id.of_string "_next" in
            let take (ctor_id, field_id) =
              let fe = CPPaccess (Aarrow, CPPvar _alt_id, field_id) in
              Sif_decl
                ( _alt_id, Tptr Tauto,
                  CPPstd_get_if (Tid (ctor_id, []), CPPunop (Uaddr, CPPvar _v_id)),
                  [ Sif (CPPbinop (Band, fe, is_sole fe),
                      unique_fence @ [Sreturn (Some (CPPmove fe))], []) ],
                  [] )
            in
            let next_lambda =
              mk_lambda
                [(Tref (Lvalue, variant_t_ty), Some _v_id)]
                (Some ptr_ty)
                (List.map take fields @ [Sreturn (Some CPPnullptr)])
                ~capture:Immediate
            in
            let body =
              [ Sasgn (next_id, Declare Tauto, next_lambda);
                Sasgn (_cur_id, Declare ptr_ty,
                  mk_call (CPPvar next_id) [mk_call (CPPvar (Id.of_string "v_mut")) []]);
                Swhile (CPPvar _cur_id,
                  [ Sasgn (_cur_id, Existing,
                      mk_call (CPPvar next_id)
                        [CPPaccess_call (Aarrow, CPPvar _cur_id, Id.of_string "v_mut", [])]) ]) ]
            in
            [(Fdestructor body, VPublic, SManipulators)]
          | _ when not has_mutual ->
            (* Self-recursive only: stack holds shared_ptr<Self> directly *)
            let stack_elem_ty = Tshared_ptr self_ty in
            let stack_ty =
              Table.mark_needs_small_vector ();
              Tid_external (Crane_rt.small_vector, [stack_elem_ty])
            in
            let _drain_id = Id.of_string "_drain" in
            let drain_lambda =
              mk_lambda
                [(Tref (Lvalue, variant_t_ty), Some _v_id)]
                None drain_stmts ~capture:Immediate
            in
            let body =
              [ Sasgn (_stack_id, Declare stack_ty,
                  CPPbraced []);
                (* Most drains only ever hold a handful of pending nodes at
                   once (worklist depth tracks tree height, not size), so
                   [crane::small_vector] keeps the first 8 elements inline
                   with no heap allocation at all, spilling to a heap
                   std::vector only if a destructor happens to drain a
                   worklist deeper than that. *)
                Sasgn (_drain_id, Declare Tauto, drain_lambda);
                Sexpr (mk_call (CPPvar _drain_id)
                  [mk_call (CPPvar (Id.of_string "v_mut")) []]);
                Swhile (
                  CPPunop (Unot,
                    CPPaccess_call (Adot, CPPvar _stack_id,
                      Id.of_string "empty", [])),
                  [ Sasgn (_cur_id, Declare Tauto,
                      CPPmove (CPPaccess_call (Adot, CPPvar _stack_id,
                        Id.of_string "back", [])));
                    Sexpr (CPPaccess_call (Adot, CPPvar _stack_id,
                      Id.of_string "pop_back", []));
                    Sif (
                      CPPbinop (Beq,
                        CPPaccess_call (Adot, CPPvar _cur_id,
                          Id.of_string "use_count", []),
                        CPPint 1),
                      unique_fence
                      @ [Sexpr (mk_call (CPPvar _drain_id)
                        [CPPaccess_call (Aarrow, CPPvar _cur_id,
                          Id.of_string "v_mut", [])])], [])
                  ])
              ]
            in
            [(Fdestructor body, VPublic, SManipulators)]
          | _, _ ->
            (* Mutual recursion: stack holds std::any to accommodate
               shared_ptrs of different types in the mutual group *)
            let stack_ty =
              Table.mark_needs_small_vector ();
              Tid_external (Crane_rt.small_vector, [Tany])
            in
            let _drain_self_id = Id.of_string "_drain_self" in
            let drain_self_lambda =
              mk_lambda
                [(Tref (Lvalue, variant_t_ty), Some _v_id)]
                None drain_stmts ~capture:Immediate
            in
            (* Build the per-partner drain logic used inside the while loop.
               For each partner type, generates an [Sif_decl] that casts the
               [std::any] stack entry to [shared_ptr<Partner>], then drains
               the partner's recursive fields into the shared stack. *)
            let gen_partner_branch (pname, pcnames, ptys, _) =
              let partner_ty = Tglob (pname, ty_vars, []) in
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
            let deref_sp = CPPderef (CPPvar _sp_id) in
            let sp_alive_and_unique =
              CPPbinop (Band, deref_sp,
                CPPbinop (Beq,
                  CPPaccess_call (Adot, deref_sp,
                    Id.of_string "use_count", []),
                  CPPint 1))
            in
            let self_branch_body =
              [Sif (sp_alive_and_unique,
                unique_fence
                @ [Sexpr (mk_call (CPPvar _drain_self_id)
                  [CPPaccess_call (Aarrow, deref_sp,
                    Id.of_string "v_mut", [])])], [])]
            in
            let rec build_if_chain branches =
              match branches with
              | [] -> []
              | (partner_ty, partner_drains) :: rest ->
                let inner = build_if_chain rest in
                let partner_body =
                  [Sif (sp_alive_and_unique,
                    Sasgn (_pv_id, Declare (Tref (Lvalue, Tauto)),
                      CPPaccess_call (Aarrow, deref_sp,
                        Id.of_string "v_mut", []))
                    :: partner_drains, [])]
                in
                [Sif_decl (_sp_id, Tptr Tauto,
                  Cpp_erasure.unbox (Tshared_ptr partner_ty)
                    (CPPunop (Uaddr, CPPvar _cur_id)),
                  partner_body, inner)]
            in
            let loop_body_stmts =
              [Sif_decl (_sp_id, Tptr Tauto,
                Cpp_erasure.unbox (Tshared_ptr self_ty)
                  (CPPunop (Uaddr, CPPvar _cur_id)),
                self_branch_body,
                build_if_chain partner_branches)]
            in
            let body =
              [ Sasgn (_stack_id, Declare stack_ty, CPPbraced []);
                Sasgn (_drain_self_id, Declare Tauto, drain_self_lambda);
                Sexpr (mk_call (CPPvar _drain_self_id)
                  [mk_call (CPPvar (Id.of_string "v_mut")) []]);
                Swhile (
                  CPPunop (Unot,
                    CPPaccess_call (Adot, CPPvar _stack_id,
                      Id.of_string "empty", [])),
                  Sasgn (_cur_id, Declare Tauto,
                    CPPmove (CPPaccess_call (Adot, CPPvar _stack_id,
                      Id.of_string "back", [])))
                  :: Sexpr (CPPaccess_call (Adot, CPPvar _stack_id,
                       Id.of_string "pop_back", []))
                  :: loop_body_stmts)
              ]
            in
            [(Fdestructor body, VPublic, SManipulators)]
      in

      (* For coinductive types, add public constructor accepting
         std::function<variant_t()> (public so make_shared can access it) *)
      let lazy_ctor =
        if is_coinductive then
          let param_name = Id.of_string "_thunk" in
          let param_ty = Tfun ([], variant_alias_ty) in
          let init_expr =
            mk_call
              (CPPvar
                 (Id.of_string_soft
                    (Crane_rt.lazy_ ^ "<" ^ variant_alias_name ^ ">") ))
              [CPPmove (CPPvar param_name)]
          in
          let init_list = [(vmn_id, init_expr)] in
          [
            ( Fconstructor
                     { fc_tparams = [];
                       fc_params = [(param_name, param_ty)];
                       fc_inits = init_list;
                       fc_body = [];
                       fc_explicit = true;
                       fc_noexcept = false },
              VPublic,
              SCreators );
          ]
        else
          []
      in

      (* 5. Static factory methods.  Each constructor gets one factory
         method as a direct static member of the struct, returning by value.

         Factory names are the lowercase of the constructor struct name
         (e.g., Cons → cons).  If this collides with a C++ keyword or the
         type's own name, the factory falls back to PascalCase with trailing
         underscore (e.g., Char → Char_).  See {!factory_name_of_ctor}.

         Move semantics: All parameters use the "sink parameter" idiom
         (passed by value, std::move'd into the struct initializer).
         Non-coinductive recursive fields take the inner type by value and
         are wrapped in make_shared internally; coinductive fields take a
         [const shared_ptr<T>&]. *)
      let ind_type_name = Common.pp_global_name Type name in

      let mk_factory_methods ret_ty build i tys_list =
        let c = cnames.(i) in
        let cname = ctor_struct_name_of_ref ~fallback_idx:i c in
        let fname =
          factory_name_of_ctor ~type_name:ind_type_name cname
        in
        let factory_name = Id.of_string fname in
        (* Convert ML types both as public API types and constructor storage
           types.  Public APIs remain value-shaped (empty ns); storage uses
           [name] in ns so non-coinductive recursive occurrences are
           [shared_ptr]-wrapped. *)
        let cpp_tys =
          List.mapi
            (fun j ty ->
              let storage_ty =
                convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name)
                  vars
                  ty
              in
              let api_ty =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  vars
                  ty
              in
              maybe_record_boxed_recursive_ind ~ind_ref:name ty;
              let storage_ty =
                if ml_type_has_nested_self_ref ~ind_ref:name ty
                   && not is_coinductive
                then
                  (* Use bare (no-ns) type so factory param and storage are
                     consistent: shared_ptr<optional<chain>> not
                     shared_ptr<optional<shared_ptr<chain>>>. *)
                  (* Boxed-element container recursion: store by value (the box
                     is the indirection); no outer shared_ptr/arena pointer. *)
                  if (not is_coinductive)
                     && ml_type_recurses_through_boxed_container ~ind_ref:name ty
                  then api_ty
                  else Tshared_ptr api_ty
                else storage_ty
              in
              let storage_ty =
                if vars = [] then
                  match storage_ty with
                  | Tshared_ptr _ ->
                    tvar_erase_type storage_ty
                  | _ when has_unnamed_tvar storage_ty -> Tany
                  | _ -> storage_ty
                else storage_ty
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
           can move in.  Coinductive shared_ptr fields stay as const ref. *)
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
        let ctor_args =
          List.map
            (fun (j, storage_ty, api_ty) ->
              let var = CPPvar (param_name_of j) in
              match storage_ty with
              | Tfun (storage_args, storage_ret) -> begin
                match api_ty with
                | Tfun (api_args, api_ret) when List.length storage_args = List.length api_args
                  && storage_ty <> api_ty ->
                  let lambda_params =
                    List.mapi
                      (fun k storage_arg ->
                        (storage_arg, Some (Id.of_string ("x" ^ string_of_int k)))
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
                  mk_lambda lambda_params (Some storage_ret)
                    [Sreturn (Some ret)] ~capture:Closure
                | _ when storage_ty = api_ty -> CPPmove var
                | _ ->
                  gen_type_conversion_expr
                    ~src_ty:api_ty ~dst_ty:storage_ty var
              end
              | Tshared_ptr inner ->
                let arg = if is_coinductive then var else CPPmove var in
                let converted =
                  if inner = api_ty then arg
                  else gen_type_conversion_expr ~src_ty:api_ty ~dst_ty:inner arg
                in
                (* Scoped-arena redesign: a single unified factory call.  For
                   arena-eligible types this is the runtime-arena-aware factory
                   ([Alloc_arena_scoped]: crane::rc<T>::make / crane::arena_make_shared)
                   which bump-allocates only when a scope is open and otherwise
                   is exactly make_shared/make_rc; NoArena / coinductive / mutual
                   types keep the plain factory. *)
                if arena_runtime_ok then
                  mk_call (CPPalloc (Alloc_arena_scoped, inner)) [converted]
                else
                  mk_call (CPPalloc (Alloc_heap, inner)) [converted]
              | _ when storage_ty = api_ty ->
                if is_trivially_copyable_type api_ty then var
                else CPPmove var
              | _ ->
                gen_type_conversion_expr
                  ~src_ty:api_ty ~dst_ty:storage_ty var )
            cpp_tys
        in
        let body = [Sreturn (Some (build i cname ctor_args))] in
        let primary =
          ( Fmethod
              (static_fun ~name:factory_name ~ret:ret_ty ~params ~body),
            VPublic,
            SCreators )
        in
        (* Perceus reuse factory (Crane Reuse): a variant [<ctor>__reuse] that
           takes a leading reuse-token parameter [_tok] and, for the single
           recursive field, allocates via [crane::make_rc_reusing(_tok, ...)]
           instead of make_shared/arena_make — recycling the token's cell in
           place when it is uniquely owned.  Only for NonAtomicRc (crane::rc
           carries the reusable control block) and single-recursive-field,
           non-coinductive constructors; the caller (a reuse-eligible match arm)
           threads a matched, uniquely-owned recursive child as the token. *)
        let n_rec_fields =
          List.length
            (List.filter
               (fun (_, storage_ty, _) ->
                 match storage_ty with Tshared_ptr _ -> true | _ -> false)
               cpp_tys )
        in
        let reuse_factory =
          if Table.reuse () && Table.non_atomic_rc ()
             && (not is_coinductive) && n_rec_fields = 1
          then
              let tok_id = Id.of_string "_tok" in
              let rec_inner =
                List.find_map
                  (fun (_, storage_ty, _) ->
                    match storage_ty with
                    | Tshared_ptr inner -> Some inner
                    | _ -> None )
                  cpp_tys
                |> Option.get
              in
              let reuse_params =
                (tok_id, Tshared_ptr rec_inner) :: params
              in
              let reuse_ctor_args =
                List.map
                  (fun a ->
                    match a with
                    | CPPfun_call (_, CPPalloc (Alloc_heap, inner), cargs)
                    | CPPfun_call
                        (_, CPPalloc (Alloc_arena_scoped, inner), cargs) ->
                      (* make_rc_reusing takes the token first. *)
                      mk_call (CPPalloc (Alloc_reusing, inner))
                        (CPPmove (CPPvar tok_id) :: call_args cargs)
                    | other -> other )
                  ctor_args
              in
              let reuse_body = [Sreturn (Some (build i cname reuse_ctor_args))] in
              [ ( Fmethod
                    (static_fun
                       ~name:(Id.of_string (fname ^ "__reuse"))
                       ~ret:ret_ty ~params:reuse_params ~body:reuse_body),
                  VPublic,
                  SCreators ) ]
          else []
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
                   (fun i cname args ->
                     let self = mk_cppglob name ty_vars in
                     if is_coinductive then
                       mk_call self
                         [mk_call lazy_cell (CPPin_place :: CPPin_place_index i :: args)]
                     else mk_call self [CPPstruct_id (Id.of_string cname, [], args)] ) )
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
          let cell_ty = Tid_external (Crane_rt.lazy_, [variant_alias_ty]) in
          let delegate =
            mk_call
              (CPPscope (lazy_cell, Id.of_string "delegate", []))
              [CPPforward (named_tvar f, CPPvar thunk)]
          in
          let body = [Sreturn (Some (mk_call (mk_cppglob name ty_vars) [delegate]))] in
          let m =
            { (static_fun ~name:(Id.of_string "lazy_") ~ret:self_ty
                 ~params:[(thunk, rval_ref (named_tvar f))] ~body)
              with mf_tparams = [(TTtypename, f)] }
          in
          (* The cell the factory builds a value around. *)
          let cell_ctor =
            let c = Id.of_string "_cell" in
            ( Fconstructor
                { fc_tparams = [];
                  fc_params = [(c, cell_ty)];
                  fc_inits = [(vmn_id, CPPmove (CPPvar c))];
                  fc_body = [];
                  fc_explicit = true;
                  fc_noexcept = false },
              VPublic,
              SCreators )
          in
          [cell_ctor; (Fmethod m, VPublic, SCreators)]
        else
          []
      in

      (* Scoped-arena redesign: the old [arena_deep_copy_ctor] (which
         deep-copied every recursive raw-pointer field on copy, the
         source of the composite-hang failure mode) is gone entirely.  Recursive
         fields are now ordinary refcounted smart pointers, so the normal copy
         path is already correct and O(1) per node. *)
      let value_copy_clone_methods =
          let converting_ctor =
            let all_fields_empty =
              Array.for_all (fun tys_list -> tys_list = []) tys
            in
            (* Scoped-arena redesign: arena-backed types are now ordinary
               recursive smart-pointer types, so the cross-instantiation
               converting constructor is generated for them exactly as for any
               other polymorphic recursive type (no special arena suppression). *)
            if vars = [] || all_fields_empty then []
            else
              let n_vars = List.length vars in
              let u_var_names =
                List.mapi
                  (fun i _ ->
                    Id.of_string
                      (if n_vars = 1 then "_U"
                       else "_U" ^ string_of_int i))
                  vars
              in
              let u_tys =
                List.map named_tvar u_var_names
              in
              let source_ty = Tglob (name, u_tys, []) in
              let n_ctors = Array.length cnames in
              let other_id = Id.of_string "_other" in
              let vmn_id = Id.of_string variant_member_name in
              let gen_branch i tys_list =
                let c = cnames.(i) in
                let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                let ctor_struct_name =
                  ctor_struct_name_of_ref ~fallback_idx:i c
                in
                let source_ctor_ty = Tid_external (Id.to_string cname_id, []) in
                let field_info =
                  List.mapi
                    (fun j ty ->
                      let field_id =
                        lookup_ctor_field_name ~owner:c ctor_struct_name j
                      in
                      let make_field_ty var_names =
                        let bare_ty =
                          convert_ml_type_to_cpp_type (empty_env ())
                            var_names ty
                        in
                        let storage_ty =
                          convert_ml_type_to_cpp_type (empty_env ()) ~ns:(Refset'.singleton name) var_names ty
                        in
                        maybe_record_boxed_recursive_ind ~ind_ref:name ty;
                        if ml_type_has_nested_self_ref ~ind_ref:name ty
                           && not is_coinductive
                        then
                          (* Boxed-element container recursion: by value. *)
                          if (not is_coinductive)
                             && ml_type_recurses_through_boxed_container
                                  ~ind_ref:name ty
                          then bare_ty
                          else Tshared_ptr bare_ty
                        else storage_ty
                      in
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
                      gen_type_conversion_expr
                        (* Every inductive generated into this same scope --
                           the type itself, its mutual siblings, and any other
                           module-local inductive -- is spelled bare here, so
                           it must not be namespace-qualified. *)
                        ~skip:(fun g ->
                          GlobRef.CanOrd.equal g name
                          || Table.same_mutual_block g name
                          || List.exists (GlobRef.CanOrd.equal g)
                               (get_local_inductives ()))
                        ~src_ty:src_fty ~dst_ty:dst_fty
                        (CPPvar field_id))
                    field_info
                in
                (source_ctor_ty, cname_id, field_info, converted)
              in
              let branches =
                List.init n_ctors (fun i -> gen_branch i tys.(i))
              in
              (* Each branch returns the source's alternative read at this
                 instantiation; see [init] below. *)
              let make_branch_body cname_id field_info converted =
                match field_info with
                | [] -> [Sreturn (Some (CPPstruct_id (cname_id, [], [])))]
                | _ ->
                  (* The alternative is named exactly as the
                     [std::holds_alternative] guard names it. *)
                  [ Sbind
                      ( List.map (fun (id, _, _) -> id) field_info,
                        CPPstd_get
                          ( Tqualified (source_ty, cname_id),
                            Some (CPPaccess_call (Adot, CPPvar other_id, Id.of_string "v", [])) ) );
                    Sreturn (Some (CPPstruct_id (cname_id, [], converted))) ]
              in
              let body =
                if n_ctors = 1 then
                  let source_ctor_ty, cname_id, field_info, converted =
                    List.hd branches
                  in
                  make_branch_body cname_id field_info converted
                else
                  (* Build if/else if/else chain *)
                  let other_v =
                    CPPaccess_call (Adot, CPPvar other_id,
                                       Id.of_string "v", [])
                  in
                  let rec build_if_chain = function
                    | [] -> CErrors.anomaly (Pp.str "iterative_destructor: empty constructor list")
                    | [(_, cname_id, field_info, converted)] ->
                      (* Last branch: no guard *)
                      make_branch_body cname_id field_info converted
                    | (_source_ctor_ty, cname_id, field_info, converted)
                      :: rest ->
                      let guard =
                        mk_call
                          (CPPstd_holds_alternative
                             (Tqualified (source_ty, cname_id)))
                          [other_v]
                      in
                      let body =
                        make_branch_body cname_id field_info converted
                      in
                      [Sif (guard, body, build_if_chain rest)]
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
                    let tt =
                      match List.nth_opt templates i with
                      | Some (tt, _) -> tt
                      | None -> TTtypename
                    in
                    (tt, u) )
                  u_var_names
              in
              let ctor_params =
                [(other_id,
                  Tref (Lvalue, Tconst source_ty))]
              in
              (* The variant is initialised, not assigned: default-constructing
                 it first needs the first alternative's fields to have a
                 default, and a field that is a tree does not.  A coinductive
                 value converts when it is forced, so the conversion is its
                 thunk, holding a copy of the source. *)
              let convert_variant ~capture =
                mk_lambda [] (Some variant_alias_ty) body ~capture
              in
              let init =
                if is_coinductive then
                  (* Through [converted_from]: a conversion back to the type
                     the source came from is the source's own cell. *)
                  mk_call
                    (CPPvar
                       (Id.of_string_soft
                          (Crane_rt.lazy_ ^ "<" ^ variant_alias_name
                          ^ ">::converted_from") ))
                    [ mk_call (CPPaccess (Adot, CPPvar other_id, Id.of_string "lazy_cell")) [];
                      convert_variant ~capture:Closure ]
                else mk_call (convert_variant ~capture:Immediate) []
              in
              (* Non-explicit: erased grammar actions produce a [List<std::any>]
                 that must implicitly recover to the concrete-element list at
                 return/assignment sites (e.g. [nt_semty] = [list (string *
                 json_value)]).  An [explicit] converting ctor makes those sites
                 fail with "no viable conversion".  Element recovery is a guarded
                 per-element [any_cast], so allowing the implicit conversion is
                 safe for well-typed extracted code. *)
              [( Fconstructor
                   { fc_tparams = tparams;
                     fc_params = ctor_params;
                     fc_inits = [(vmn_id, init)];
                     fc_body = [];
                     fc_explicit = false;
                     fc_noexcept = false },
                 VPublic, SCreators )]
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
          [ ( Fmethod
                {
                  mf_name = Id.of_string "lazy_cell";
                  mf_globref = None;
                  mf_tparams = [];
                  mf_ret_type =
                    Tconst
                      (Tref (Lvalue, Tid_external
                            (Crane_rt.lazy_, [variant_alias_ty])));
                  mf_params = [];
                  mf_body = [Sreturn (Some (CPPvar vmn_id))];
                  mf_receiver = Instance { this_pos = 0; is_const = true; ref_qual = Rq_any };
                  mf_is_inline = false;
                  mf_no_pure = false;
                  mf_is_noexcept = false;
                  mf_is_conversion = false;
                },
              VPublic,
              SAccessors ) ]
      in
      (* Add public accessor for v_ to enable pattern matching from outside *)
      let v_accessor =
        if is_coinductive then
          (* For coinductive: const variant_t& v() const { return
             lazy_v_.force(); } *)
          ( Fmethod
              {
                mf_name = Id.of_string "v";
                mf_globref = None;
                mf_tparams = [];
                mf_ret_type =
                  Tconst (Tref (Lvalue, variant_alias_ty));
                mf_params = [];
                mf_body =
                  [
                    Sreturn
                      (Some
                         (mk_call
                            (CPPaccess
                               (Adot, CPPvar vmn_id, Id.of_string "force"))
                            [] ) );
                  ];
                mf_receiver = Instance { this_pos = 0; is_const = true; ref_qual = Rq_any };
                mf_is_inline = false;
                mf_no_pure = false;
                mf_is_noexcept = false;
                mf_is_conversion = false;
              },
            VPublic,
            SAccessors )
        else (* For inductive: const variant_t& v() const { return v_; } *)
          ( Fmethod
              {
                mf_name = Id.of_string "v";
                mf_globref = None;
                mf_tparams = [];
                mf_ret_type =
                  Tconst (Tref (Lvalue, variant_alias_ty));
                mf_params = [];
                mf_body = [Sreturn (Some (CPPvar vmn_id))];
                mf_receiver = Instance { this_pos = 0; is_const = true; ref_qual = Rq_any };
                mf_is_inline = false;
                mf_no_pure = false;
                mf_is_noexcept = false;
                mf_is_conversion = false;
              },
            VPublic,
            SAccessors )
      in

      (* Add mutable accessor for reuse optimization (Phase 3). For
         non-coinductive types: variant_t& v_mut() { return v_; } Not generated
         for coinductive types (lazy evaluation complicates reuse). *)
      let v_mut_accessor =
        if is_coinductive then
          []
        else
          [
            ( Fmethod
                {
                  mf_name = Id.of_string "v_mut";
                  mf_globref = None;
                  mf_tparams = [];
                  mf_ret_type = Tref (Lvalue, variant_alias_ty);
                  mf_params = [];
                  mf_body = [Sreturn (Some (CPPvar vmn_id))];
                  mf_receiver = Instance { this_pos = 0; is_const = false; ref_qual = Rq_any };
                  mf_is_inline = true;
                  mf_no_pure = true;
                  mf_is_noexcept = false;
                  mf_is_conversion = false;
                },
              VPublic,
              SManipulators );
          ]
      in

      (* 6. Generate methods from method candidates using shared helper *)
      let method_fields =
        List.map (gen_single_method name vars) method_candidates
      in

      (* Detect if any method contains shared_from_this (i.e., returns 'this').
         If so, the struct needs to inherit from
         std::enable_shared_from_this. *)
      let needs_shared_from_this =
        List.exists
          (fun (fld, _vis, _tag) ->
            match fld with
            | Fmethod {mf_body; _} ->
              List.exists stmt_has_shared_from_this mf_body
            | _ -> false )
          method_fields
      in

      (* Categorize user methods: const methods are ACCESSORS, non-const are
         MANIPULATORS *)
      let method_fields =
        List.map
          (fun (fld, vis, _tag) ->
            match fld with
            | Fmethod {mf_receiver = Instance {is_const = true; _}; _} ->
              (fld, vis, SAccessors)
            | Fmethod _ -> (fld, vis, SManipulators)
            | _ -> (fld, vis, SNoTag) )
          method_fields
      in
      (* Split methods into manipulators and accessors *)
      let method_manipulators =
        List.filter (fun (_, _, tag) -> tag = SManipulators) method_fields
      in
      let method_accessors =
        List.filter (fun (_, _, tag) -> tag <> SManipulators) method_fields
      in

      (* BDE field ordering: public: constructor structs, variant_using (TYPES)
         private: variant_member (DATA)
         public: public_ctors + lazy_ctor + factory methods (CREATORS),
         v_mut + manipulators (MANIPULATORS),
         v_accessor + const methods (ACCESSORS) *)
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
           needs eliminated.  Restoring real moves does expose code that reads
           a value after moving from it -- the loopify fix-ups (invariant
           parameters are never moved from, and neither are prvalues or
           borrowed cells) exist because the copy fallback used to hide exactly
           those bugs. *)
        @ (match iterative_destructor with
           | _ :: _ -> [(Fdefaulted_special_members, VPublic, SManipulators)]
           | [] -> [])
        @ v_mut_accessor
        @ method_manipulators
        @ [v_accessor]
        @ lazy_cell_accessor
        @ method_accessors
      in

      (* Just the struct itself - no extra namespace wrapper *)
      Dstruct
        {
          ds_ref = name;
          ds_fields = all_fields;
          ds_tparams = templates;
          ds_constraint = None;
          ds_needs_shared_from_this = needs_shared_from_this;
        }

(** Generate methods for eponymous records. Uses the shared gen_single_method
    helper for records where methods are generated directly on the module struct
    (which has record fields merged). name: the record's GlobRef (e.g., IndRef
    for CHT) vars: the type variables of the record (e.g., [K; V] for CHT<K, V>)
    method_candidates: list of (func_ref, body, type, this_position) tuples *)
let gen_record_methods (name : GlobRef.t) (vars : Id.t list) method_candidates =
  List.map (gen_single_method name vars) method_candidates
 
