(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Monadic effects: [ret] and [bind] of a monad mapped to an effect
    ({!Core_effects}), sequenced as statements in sequential mode and kept
    as interaction-tree constructors in reified mode. *)

open Common
open Names
open Core_util
open Table
open Util
open Translation_state
open Type_util
open Translation_support
open Translation_types
open Translation_knot

(** [ret] of an effect monad, the global [use] (at [r]) applied to [a1 :: l],
    in expression position: the returned value in sequential mode, an
    [ITree<R>::ret] in reified mode. *)
let gen_return_expr env ~r ~use ~a1 ~l : Cpp_ir.Lowered.Expr.t =
  let ret_tys = Core_util.written_type_args use in
  if not (is_sequential_effect Core_effects.Return use) then begin
    (* Reified mode: Ret produces ITree<R>::ret(value). Don't strip it. *)
    let t = Common.last (a1 :: l) in
    match t with
    | Core.Expr.Global {callee = g; _} when is_ghost g ->
      mk_itree_ret Void []
    | _ ->
      let inner = gen_expr env t in
      (* The result type is the type argument written for the variable the
         returned value is at: [Ret : forall E R, R -> itree E R].  One
         extraction could not read says nothing. *)
      let r_cpp =
        let value_var =
          match List.rev (Type_util.core_value_domains (find_type r)) with
          | Core.Type.Variable {variable = j; _} :: _ -> Some j
          | _ -> None
        in
        match Option.bind value_var (Core_util.Var_types.find_tvar ret_tys) with
        | Some r_core when not (Core_util.is_erased_type r_core) -> cpp_of_core env r_core
        | _ -> Void
      in
      mk_itree_ret r_cpp [inner]
  end
  else begin
    let t = Common.last (a1 :: l) in
    gen_expr env t
  end

(** [bind] of an effect monad in sequential mode, the application [a], in
    expression position: an immediately invoked lambda over the statements
    that sequence it. *)
let gen_bind_expr env (a : Core.Expr.t) : Cpp_ir.Lowered.Expr.t =
  (* Sequential mode: bind in expression context (e.g., nested inside
     another expression). Wrap in IIFE so gen_stmts can sequentialize. *)
  with_escape_analysis (fun () -> with_region a (fun () ->
    Cpp_ir.Build.iife None (gen_stmts env (fun x : Cpp_ir.Lowered.Stmt.t -> Return (Some x)) a) ) )

(** [bind] of an effect monad, the global [use] (at [r]) applied to
    [a1 :: a2 :: l], in statement position ending in [k]: the action's
    statements, its result bound for the continuation in sequential mode, the
    [bind] call as an expression in reified mode. *)
let gen_bind_stmts ~slot env (k : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) (ast : Core.Expr.t) ~r ~use ~a1 ~a2
  ~l : Cpp_ir.Lowered.Stmt.t list =
  let bind_tys = Core_util.written_type_args use in
  (* The action's result type: the argument written for the variable the
     continuation takes, [A] in [bind : forall A B, M A -> (A -> M B) -> M
     B].  One extraction could not read ({!Extraction.observe_type_arg}: a
     type constructor such as an HKT carrier) says nothing. *)
  let action_result_ty =
    match List.rev (Type_util.core_value_domains (find_type r)) with
    | Core.Type.Arrow {parameter = Core.Type.Variable {variable = j; _}; _} :: _ -> (
      match Core_util.Var_types.find_tvar bind_tys j with
      | Some t when not (Core_util.is_erased_type t) -> Some t
      | _ -> None )
    | _ -> None
  in
  (* Reified mode: bind is a real function call, not desugared. *)
  if not (is_sequential_effect Core_effects.Bind use) then
    inline_iife k ((gen_expr ~slot env ast))
  else begin
    (* Sequential mode: desugar bind into sequential statements. *)
    let a_core, f = Common.last_two (a1 :: a2 :: l) in
    let a = gen_expr env a_core in
    let ids', f = collect_lams f in
  let ids, env =
    push_vars'
      (List.map (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty)) ids')
      env
  in
  push_binders env ids;
  let bound_by_bind env = core_binder ~site:(Binding (Core.Global_use.occurrence use)) env 1 in
  (* Where a machine resumes at the continuation's parameter, which of
     what its frame keeps the save moves is the plan's, as at a let. *)
  ( match (ids, Ownership_ir.save_moves (!tctx).lexical.move_plan (Core.Global_use.occurrence use)) with
  | _ :: _, Some moved -> Option.iter (fun b -> Ownership_ir.Frame_save.record b moved) (bound_by_bind env)
  | _ -> () );
  (
  match ids with
  | (x, core_ty) :: _ ->
    let ty = cpp_of_core env core_ty in
    if (match ty with Void | Obligation Unresolved_type -> true | _ -> false) || core_type_is_unit core_ty then
      (* Unit/void bind result: execute the action for side effects,
         then declare the variable as Unit::e_TT so the continuation
         can reference it if needed. *)
      let action_is_pure_ret =
        match a_core with
        | Core.Expr.Apply {callee = Core.Expr.Global use; _} -> is_effect Core_effects.Return use
        | _ -> false
      in
      let side_effect : Cpp_ir.Lowered.Stmt.t list =
        match a with
        | Enum_value _ -> []
        | _ when action_is_pure_ret -> []
        | _ -> [Expression a]
      in
      (* Generate the continuation first, then check if the variable is
         actually referenced in the generated C++ (unit-match elimination
         and Ret-in-void optimization may drop ML-level references). *)
      let body = gen_stmts ~slot env k f in
      let cpp_ty = cpp_of_core env core_ty in
      let decl : Cpp_ir.Lowered.Stmt.t list =
        if not (stmts_reference_var x body) then []
        else if core_type_is_unit core_ty && not (is_cpp_unit_type cpp_ty) then
          []
        else if core_type_is_unit core_ty then
          [Bind_variable (x, Declare (cpp_ty, bound_by_bind env), mk_tt_expr ())]
        else
          []
      in
      side_effect @ decl @ body
    else begin
      match extract_block_template a with
      | Some (ref, tmpl, args, tys) ->
        (Foreign_block
          { custom = ref;
            template = tmpl;
            result = x;
            result_type = ty;
            values = args;
            type_args = tys;
            binder = bound_by_bind env } : Cpp_ir.Lowered.Stmt.t)
        :: gen_stmts ~slot env k f
      | None ->
        (Bind_variable (x, Declare (ty, bound_by_bind env), a) : Cpp_ir.Lowered.Stmt.t) :: gen_stmts ~slot env k f
    end
  | _ ->
    (* No lambda parameters (eta-reduced continuation like bare Ret).
       Execute the action for side effects, then run the continuation. *)
    let side_effect : Cpp_ir.Lowered.Stmt.t list =
      match a with Enum_value _ -> [] | _ -> [Expression a]
    in
    ( match f with
    | Core.Expr.Global use when is_effect Core_effects.Return use ->
      (* Eta-reduced Ret: bind action Ret = action (monad right identity).
         In sequential mode, just execute the action and return. *)
      if returns_void () then
        side_effect @ [(Return None : Cpp_ir.Lowered.Stmt.t)]
      else
        [k a]
    | _ ->
      (* Eta-reduced non-Ret continuation: f is a bare function reference.
         Bind action result to a temp var and apply f to it, instead of
         discarding the result and returning f unapplied. *)
      let non_void_ty =
        match action_result_ty with
        | Some ty ->
          let cpp_ty =
            cpp_of_core env ty
          in
          if cpp_ty = Void || cpp_ty = Obligation Unresolved_type || core_type_is_unit ty then
            None
          else
            Some (cpp_ty, Ownership_ir.worth_moving ty)
        | None -> None
      in
      ( match non_void_ty with
      | Some (cpp_ty, worth_moving) ->
        let temp_id = Id.of_string "_bind_result" in
        let f_expr = gen_expr env f in
        (* The continuation is the temporary's one reader. *)
        let result : Cpp_ir.Lowered.Expr.t = if worth_moving then Move (Local temp_id) else Local temp_id in
        let app = Cpp_ir.Build.call f_expr [result] in
        [Bind_variable (temp_id, Declare (cpp_ty, None), a); k app]
      | None ->
        side_effect @ gen_stmts ~slot env k f ) ) )
  end

(** [ret] of an effect monad, [use] applied to [a1 :: l], in statement
    position ending in [k]. *)
let gen_return_stmts ~slot env (k : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) (ast : Core.Expr.t) ~use ~a1 ~l :
  Cpp_ir.Lowered.Stmt.t list =
  if not (is_sequential_effect Core_effects.Return use) then begin
    (* Reified mode: Ret is a constructor call, not desugared. *)
    inline_iife k ((gen_expr ~slot env ast))
  end
  else begin
    (* Sequential mode: eliminate Ret, just use the value. *)
    let t = Common.last (a1 :: l) in
    if returns_void () then
      (* Void-returning function: discard the value and return. *)
      [Return None]
    else
      [k (gen_expr ?expected_ty:(position_cpp_ty None) env t)]
  end
