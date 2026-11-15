(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Statements: an expression in statement position, ending in a
    continuation ([k]) that says what its value becomes.  Lets bind locals;
    local functions, effects and record matches go to their modules. *)

open Common
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Core_query
open Translation_support
open Translation_types
open Translation_knot
open Translation_match

let rec gen_stmts ?(slot = empty_slot) env (k : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) ast :
    Cpp_ir.Lowered.Stmt.t list =
  (* Statements open a position of their own and state no type for it: the
     value a [return] here carries goes to the enclosing function, not to the
     position the caller's expression was being built for.  What a tail
     statement lands in is {!with_cpp_return_type}, which
     {!position_cpp_ty} falls back to. *)
  match ast with
  | Core.Expr.Let {binder_type = let_ty;
                   value = ((Core.Expr.Fixpoint {selected = x;
                                                 functions = ids;
                                                 bodies = funs;
                                                 occurrence = occ} | Core.Expr.Cofixpoint {selected = x;
                                                                                           functions = ids;
                                                                                           bodies = funs;
                                                                                           occurrence = occ}) as fix_term);
                   body = b;
                   occurrence = let_occ; _}
    as _whole ->
    Translation_local_functions.gen_let_fix ~slot env k ~let_ty ~x ~ids ~funs ~occ ~fix_term ~b ~let_occ
  | Core.Expr.Let {binder = x; binder_type = t; value = (Core.Expr.Lambda _ as a); body = b; occurrence = let_occ} ->
    Translation_local_functions.gen_let_lambda ~slot env k ~x ~t ~a ~b ~let_occ
  | Core.Expr.Let {binder = x; binder_type = t; value = a; body = b; occurrence = let_occ} ->
    let x' = cpp_id_of_id (id_of_mlid x) in
    let ids_renamed, env' = push_vars' [(x', t)] env in
    let x_renamed = fst (List.hd ids_renamed) in
    (* The right-hand side is not under the binder, so it keeps [env]'s de
       Bruijn list -- shifting it would misread every index in it.  But
       [x_renamed] is already spoken for by the time the right-hand side runs,
       so a binder the right-hand side introduces has to be freshened against
       it too: [let x := match o with Some x => x end in ...] otherwise names
       the branch binder [x] as well and the assignment reads [x = x].  The
       names come from [env], the avoid set from [env']. *)
    let env_rhs = (fst env, snd env') in
    if x == Core.Binder_name.Anonymous then (
      push_binders env [(x_renamed, t)];
      gen_stmts ~slot env' k b )
    else if ml_type_is_unit t then (
      (* Unit-typed let bindings: the RHS may call a void-ified function,
         so we can't assign its result to a variable.  Execute the RHS for
         side effects, then declare the variable as Unit::e_TT (its only
         possible value) so the body can still reference it. *)
      let rhs = gen_stmts env_rhs (fun e -> Expression e) a in
      push_binders env [(x_renamed, t)];
      (* Drop trivially pure RHS (e.g. Unit::e_TT from tt, variable refs) *)
      let rhs = List.filter (fun (s : Cpp_ir.Lowered.Stmt.t) ->
        match s with
        | Expression (Enum_value _) -> false
        | Expression (Local _) -> false
        | _ -> true) rhs in
      (* Generate the body first, then check if the variable is actually referenced in the
         generated C++ (not just the ML AST, since optimizations like
         unit-match elimination may drop references). *)
      let body =
        gen_stmts ~slot env' k b
      in
      let decl : Cpp_ir.Lowered.Stmt.t list =
        if stmts_reference_var x_renamed body then
          let cpp_ty = cpp_of_ml env t in
          [Bind_variable (x_renamed, Declare (cpp_ty, core_binder ~site:(Binding let_occ) env' 1), mk_tt_expr ())]
        else []
      in
      rhs @ decl @ body )
    else
      let depth = (!tctx).current_letin_depth in
      tctx := { !tctx with current_letin_depth = depth + 1 };
      (* Where a machine resumes at this let, which of what its frame keeps
         the save moves is the plan's: the machine reads it by the let's
         binder. *)
      ( match (Ownership_ir.save_moves (!tctx).move_plan let_occ, core_binder ~site:(Binding let_occ) env' 1) with
      | Some moved, Some binder -> Ownership_ir.Frame_save.record binder moved
      | _ -> () );
      (* What the continuation reads, in the right-hand side's coordinates. *)
      let cont_free = Escape.free_rels 1 b in
      let asgn =
        (* Single-use partial application optimization: when the RHS is a partial
           application and the bound variable is used at most once in the
           continuation without escaping, AND all free variables of the RHS are
           dead in the continuation (so [&] capture references stay valid),
           tell eta_fun to keep CPPmove wrappers and use [&] capture for
           zero-copy closure generation. *)
        let is_single_use_partial_app =
          match a with
          | Core.Expr.Apply {callee = head; arguments = ml_args}
          | Core.Expr.Coerce {value = Core.Expr.Apply {callee = head; arguments = ml_args}; _}
          | Core.Expr.Boxed_value {value = Core.Expr.Apply {callee = head; arguments = ml_args}; _}
          | Core.Expr.Lambda_group_barrier {value = Core.Expr.Apply {callee = head; arguments = ml_args}; _} ->
            (match Escape.partial_app_remaining head ml_args with
             | Some remaining ->
               Escape.nb_occur_match 1 b <= 1
               && not (Escape.escapes 1 b)
               && Escape.IntSet.is_empty
                    (Escape.IntSet.inter (Escape.free_rels 0 a) cont_free)
               && Escape.single_use_nargs 1 b >= remaining
             | None -> false)
          | _ -> false
        in
        let afun v : Cpp_ir.Lowered.Stmt.t = Bind_variable (x_renamed, Existing, v) in
        (* Thread the let-binding's type annotation as the expected ML type
           so that gen_ctor_call can recover the concrete element type for
           constructors (like nil) whose ML annotation has unresolved metas or
           erased type args.  For example: let sk = [] : list parser_frame — the
           let-binding knows the element type even when the nil's own annotation
           has Core.Type.Erased Core.Erasure_reason.Type_argument. *)
        (* Look ahead: if t has erased type args, look at the body b to see if the
           bound var (Core.Expr.Bound_variable 1 in b) is used as the i-th arg of a constructor call
           with a non-erased corresponding type arg. If so, use that type instead of t.
           This recovers the correct element type for nils bound before pair constructors:
             let empty_stack : list(Core.Type.Meta) = [] in make_pair(fr, empty_stack)
           where the pair type says the second arg is list(parser_frame). *)
        let t_effective =
          let t_has_erased = ml_type_contains_erased t in
          if not t_has_erased then t
          else begin
            (* Try to infer from an Core.Expr.Construct that immediately follows in the body.
               The body b may be directly an Core.Expr.Construct, or wrapped in one more Core.Expr.Let. *)
            let try_cons_body (b_inner : Core.Expr.t) db_offset =
              (* db_offset: how many let-bindings above b_inner, so Core.Expr.Bound_variable (1+db_offset) = x *)
              let target_rel = 1 + db_offset in
              (* Resolve t to get the underlying inductive (through metas) *)
              let t_ind_opt = match resolve_tmeta t with
                | Core.Type.Global_app {head = t_ind; _} -> Some t_ind
                | _ -> None
              in
              match b_inner with
              | Core.Expr.Construct {result_type = ctor_ty; arguments = ts; _} ->
                let result = ref None in
                List.iteri (fun i (ti : Core.Expr.t) ->
                  match ti with
                  | Core.Expr.Bound_variable {index = r; _} when r = target_rel ->
                    (match resolve_tmeta ctor_ty with
                     | Core.Type.Global_app {type_arguments = ctor_tys; _} ->
                       (match List.nth_opt ctor_tys i with
                        | Some raw_candidate ->
                          (match resolve_tmeta raw_candidate with
                          | Core.Type.Global_app {head = ind; type_arguments = sub_tys; _} as candidate ->
                            (* Check that candidate's inductive matches t's inductive.
                               When t is fully erased (Core.Type.Meta{None}), accept any concrete type. *)
                            let matches_t = match t_ind_opt with
                              | Some t_ind -> GlobRef.CanOrd.equal ind t_ind
                              | None -> true
                            in
                            if matches_t && not (List.exists is_erased_ml_type sub_tys) then
                              result := Some candidate
                          | _ -> ())
                        | _ -> ())
                     | _ -> ())
                  | _ -> ()
                ) ts;
                !result
              | _ -> None
            in
            (* Try to infer t from an Core.Expr.Apply body: find the position of target_rel
               in the application args, look up the function's ML type, and extract
               the type of that arg.  This handles the pattern:
                 let sk0 : Core.Type.Meta = (fr, nil) in multistep(..., sk0, ...)
               where multistep's type tells us sk0 has type parser_frame × list(parser_frame). *)
            let try_app_body (b_inner : Core.Expr.t) db_offset =
              let target_rel = 1 + db_offset in
              match b_inner with
              | Core.Expr.Apply {callee = Core.Expr.Global {callee = func_ref; _}; arguments = app_args} ->
                let rec find_pos args i =
                  match args with
                  | [] -> None
                  | (Core.Expr.Bound_variable {index = r; _}) :: _ when r = target_rel -> Some i
                  | ( Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = r; _}; _}
                    | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = r; _}; _}
                    | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = r; _}; _} ) :: _
                    when r = target_rel -> Some i
                  | _ :: rest -> find_pos rest (i + 1)
                in
                (match find_pos app_args 0 with
                | None -> None
                | Some idx ->
                  (match find_type_opt func_ref with
                  | None -> None
                  | Some func_ty ->
                    let rec nth_arg ty n =
                      match ty with
                      | Core.Type.Arrow {parameter = Core.Type.Erased _; result = cod} -> nth_arg cod n
                      | Core.Type.Arrow {parameter = dom; _} when n = 0 -> Some dom
                      | Core.Type.Arrow {result = cod; _} -> nth_arg cod (n - 1)
                      | Core.Type.Meta {contents = Some t2} -> nth_arg t2 n
                      | _ -> None
                    in
                    let try_unfold_typedef resolved =
                      match resolved with
                      | Core.Type.Global_app {head = GlobRef.ConstRef kn; _} ->
                        (match Table.lookup_typedef_unchecked kn with
                         | Some expanded -> expanded
                         | None -> resolved)
                      | _ -> resolved
                    in
                    (match nth_arg func_ty idx with
                    | Some arg_ty ->
                      let resolved = resolve_tmeta arg_ty in
                      let resolved = try_unfold_typedef resolved in
                      (match resolve_tmeta t, resolved with
                      | _, Core.Type.Global_app {type_arguments = r_sub; _}
                        when not (List.exists is_erased_ml_type r_sub) ->
                        Some resolved
                      | _ -> None)
                    | None -> None)))
              | _ -> None
            in
            let inferred = match (b : Core.Expr.t) with
              | Core.Expr.Construct _ -> try_cons_body b 0
              | Core.Expr.Let {value = a'; _} ->
                (* In body = Core.Expr.Let(sk0, pair_expr, ...), nil is at Core.Expr.Bound_variable 1 in pair_expr.
                   db_offset=0 because pair_expr is evaluated before sk0 is bound. *)
                (match try_cons_body a' 0 with
                 | Some _ as r -> r
                 | None -> try_cons_body b 0)
              | Core.Expr.Apply _ ->
                (* Body is a function application — look up the function type to find
                   the type expected for the bound variable at its argument position. *)
                try_app_body b 0
              | _ -> None
            in
            match inferred with Some ty -> ty | None -> t
          end
        in
        (* The bound value is not the enclosing function's result, so the
           result a position falls back to when it states nothing is the
           binder's own type, where it says one: [let t := x <- arg ;; ...]
           is a tree over [arg]'s family, whatever family the function
           returns into. *)
        let rhs_result =
          let c = cpp_of_ml env t_effective in
          (* A binder erasure took the whole type from -- [nt_semty x], a
             type computed from a value -- holds a box, and its value is
             one; read at the function's result instead, it is cast to a
             type it does not have. *)
          if Cpp_ir.Types.prints_as_any c then Some c
          else if ml_type_contains_erased t_effective then current_cpp_return_type ()
          else
            match spell_in_scope c with
            | Some _ as t -> t
            | None -> current_cpp_return_type ()
        in
        with_cpp_return_type rhs_result (fun () ->
          gen_stmts
            ~slot:
              { slot with
                repr = Native;
                expected_ml_ty = Some t_effective;
                eta_keep_moves = is_single_use_partial_app }
            env_rhs afun a )
      in
      (* Push env_types AFTER generating the value expression [a] — [a] uses de
         Bruijn indices that don't include the new let binding.  The body [b]
         (generated below) does include it. *)
      let t_for_env = if stmts_yield_boxed asgn then Core.Type.Erased Core.Erasure_reason.Type_argument else t in
      push_binders env [(x_renamed, t_for_env)];
      (* Const-ref binding: a record field projected out of a variable not
         moved there is bound as [const T&], saving a [shared_ptr] count
         bump; the plan does not own such a binder, so it is never moved
         from.  Only for [shared_ptr] types. *)
      let use_const_ref = Ownership_ir.projects_in_place (!tctx).move_plan t a in
      let result =
        match asgn with
          | [Bind_variable (_, Existing, e)] ->
            let cpp_ty = cpp_of_ml env t in
            (* When the type contains Tany (from erased carrier projections) but
               the generated expression is a lambda with concrete types, derive
               the std::function type from the lambda's parameter and return
               types. *)
            let cpp_ty : Cpp_ir.Lowered.Type.t =
              match (cpp_ty, e) with
              | Function (dom, _), Lambda
                { params = params;
                  return_type = Some ret_ty;
                  _ }
                when List.exists Ml_type_util.has_tany_in_type dom ->
                let strip_tmod : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
                  | Const t -> t
                  | t -> t
                in
                let param_tys =
                  List.map (fun (ty, _) -> strip_tmod ty) params
                in
                Function (param_tys, ret_ty)
              | _, Lambda _ -> cpp_ty
              | _, _
                when Ml_type_util.has_erased_type_in_type cpp_ty
                     || Cpp_ir.Types.exists
                          (fun (t : Cpp_ir.Lowered.Type.t) -> match t with Promoted_member _ -> true | _ -> false)
                          cpp_ty ->
                (* Type contains erased positions (Tany or dummy_type marker)
                   but the expression is not a lambda with inferable types.
                   Use [auto] so the C++ compiler deduces the concrete type
                   from the RHS — e.g. for pair-projection bindings like
                   [const auto &prs = tup.first] where the erased type would
                   be [List<pair<String, any>>] but the actual type of
                   [tup.first] is [List<pair<String, JV>>], or for existT nil
                   constructors where the element type is dummy_type. *)
                Auto
              | _ -> cpp_ty
            in
            (* Apply const-ref binding when safe. *)
            let cpp_ty : Cpp_ir.Lowered.Type.t =
              if use_const_ref then Reference (Lvalue, Const cpp_ty)
              else cpp_ty
            in
            begin match extract_block_template e with
            | Some (ref, tmpl, args, tys) ->
              (Foreign_block
                { custom = ref;
                  template = tmpl;
                  result = x_renamed;
                  result_type = cpp_ty;
                  values = args;
                  type_args = tys;
                  binder = core_binder ~site:(Binding let_occ) env' 1 } : Cpp_ir.Lowered.Stmt.t)
              :: gen_stmts ~slot env' k b
            | None ->
              (Bind_variable (x_renamed, Declare (cpp_ty, core_binder ~site:(Binding let_occ) env' 1), e) : Cpp_ir.Lowered.Stmt.t)
              :: gen_stmts ~slot env' k b
            end
          | _ ->
            let cpp_ty = cpp_of_ml env t in
            ((Declare (x_renamed, cpp_ty, core_binder ~site:(Binding let_occ) env' 1) : Cpp_ir.Lowered.Stmt.t) :: asgn)
            @ gen_stmts ~slot env' k b
      in
      result
  | Core.Expr.Apply {callee = ((Core.Expr.Fixpoint {selected = x;
                                                    functions = ids;
                                                    bodies = funs;
                                                    occurrence = occ} | Core.Expr.Cofixpoint {selected = x;
                                                                                              functions = ids;
                                                                                              bodies = funs;
                                                                                              occurrence = occ}) as fix_term);
                     arguments = args} ->
    Translation_local_functions.gen_applied_fix ~slot env k ~x ~ids ~funs ~occ ~fix_term ~args
  | Core.Expr.Fixpoint {selected = x;
                        functions = ids;
                        bodies = funs;
                        occurrence = occ} | Core.Expr.Cofixpoint {selected = x;
                                                                  functions = ids;
                                                                  bodies = funs;
                                                                  occurrence = occ} as fix_term ->
    Translation_local_functions.gen_standalone_fix env k ~x ~ids ~funs ~occ ~fix_term
  (* | Core.Expr.Apply (Core.Expr.Global {callee = h; _}, a1 :: a2 :: l) when is_hoist h -> gen_stmts env k
     (Core.Expr.Apply (a1, a2::[])) *)
  | Core.Expr.Apply {callee = Core.Expr.Global ({callee = r; _} as use);
                     arguments = a1 :: a2 :: l} when is_effect Core_effects.Bind use ->
    Translation_effects.gen_bind_stmts ~slot env k ast ~r ~use ~a1 ~a2 ~l
  | Core.Expr.Apply {callee = Core.Expr.Global use; arguments = a1 :: l} when is_effect Core_effects.Return use ->
    Translation_effects.gen_return_stmts ~slot env k ast ~use ~a1 ~l
  | Core.Expr.Match {scrutinee_type = typ;
                     scrutinee = t;
                     branches = pv;
                     occurrence = case_occ} when Core_elaborate.match_kind typ pv case_occ = Match_kind.Custom ->
    gen_custom_cpp_case env k typ t pv case_occ
  | Core.Expr.Construct {constructor = r; arguments = []; _} when Table.is_tt_constructor r
      && returns_void () ->
    (* tt (unit constructor) in tail position of a void-returning function *)
    if (!tctx).itree_mode = Reified then [k (mk_itree_ret Void [])]
    else
      [Return None]
  | Core.Expr.Global {callee = r; _} when is_ghost r ->
    if (!tctx).itree_mode = Reified then
      (* Reified mode: ghost (void value) at tail position must produce
         ITree<void>::ret() rather than bare return, since the function
         returns shared_ptr<ITree<void>>. *)
      [k (mk_itree_ret Void [])]
    else
      [Return None]
  | Core.Expr.Runtime_error msg ->
    (* Generate throw statement for unreachable/absurd cases (e.g., empty
       match) *)
    [Throw msg]
  | Core.Expr.Coerce {value = Core.Expr.Runtime_error msg; _} | Core.Expr.Boxed_value {value = Core.Expr.Runtime_error msg; _} | Core.Expr.Lambda_group_barrier {value = Core.Expr.Runtime_error msg; _} ->
    (* Handle Core.Expr.Runtime_error wrapped in a coercion *)
    [Throw msg]
  | Core.Expr.Match {scrutinee_type = typ;
                     scrutinee = t;
                     branches = pv;
                     occurrence = case_occ} when Match_kind.is_record (Core_elaborate.match_kind typ pv case_occ) ->
    Translation_match.gen_record_match_stmts ~slot env k ast ~typ ~t ~pv ~case_occ
  | t ->
    (* Tail position.  No deref_reified needed: in sequential mode, monadic
       variables are direct values (bind desugars to let-binding); in
       reified mode, they are trees returned as-is. *)
    let is_void_tail = match t with
      | Core.Expr.Apply {callee = f; arguments = args}
      | Core.Expr.Coerce {value = Core.Expr.Apply {callee = f; arguments = args}; _}
      | Core.Expr.Boxed_value {value = Core.Expr.Apply {callee = f; arguments = args}; _}
      | Core.Expr.Lambda_group_barrier {value = Core.Expr.Apply {callee = f; arguments = args}; _} ->
        ml_callee_is_void f
        (* Only treat as void if fully applied — partial applications
           return a function value, not void. *)
        && ( match f with
           | Core.Expr.Global {callee = r; _} ->
             ( match find_type_opt r with
             | Some ty ->
               let n_non_dummy_args =
                 List.length (List.filter (fun a ->
                   match a with Core.Expr.Erased_value _ -> false | _ -> true) args)
               in
               n_non_dummy_args >= count_ml_value_arrows ty
             | None -> true )
           | _ -> true )
      | _ -> false
    in
    if is_void_tail then begin
      let e = gen_expr ~slot ?expected_ty:(position_cpp_ty None) env t in
      if returns_void () then
        [Expression e; Return None]
      else
        match (k (Literal (Int 0)) : Cpp_ir.Lowered.Stmt.t) with
        | Expression _ ->
          (* Side-effect-only continuation (e.g. from unit let handler).
             The void call provides the side effect; the caller handles
             the variable declaration separately.  No value needed. *)
          [Expression e]
        | _ ->
          [(Expression e : Cpp_ir.Lowered.Stmt.t)]
          @ inline_iife k ((mk_tt_expr ()))
    end
    else begin
      (* Whether this continuation is the function's result rather than a
         binding.  Probing [k] is how the void case above already asks. *)
      let k_returns = match k (Literal (Int 0)) with Return _ -> true | _ -> false in
      let e = gen_expr ~slot ?expected_ty:(position_cpp_ty None) env t in
      (* A pair accessor applied to an erased pair yields a [std::any] at run
         time even though its ML type is concrete.  In tail position that value
         is the result, so cast it back to the declared return type -- the same
         recovery the let-binding path performs by marking the bound variable
         erased. *)
      let e =
        match current_cpp_return_type () with
        | Some rt when k_returns -> (
          match slot_repr_of_cpp_type rt with
          | Boxed Family_box -> deep_box_list t e
          | Boxed Var_box -> e
          | Native -> recover_boxed_component rt e )
        | _ -> e
      in
      inline_iife k (e)
    end
