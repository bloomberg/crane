(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Monadic effects: [ret] and [bind] of a monad mapped to an effect
    ({!Core_plan.Effects}), sequenced as statements in sequential mode and kept
    as interaction-tree constructors in reified mode.  One of the modules
    lowering Core bodies to CppIR that {!Lower_expr} drives. *)

open Base.Common
open Names
open Base.Core_util
open Base.Table
open Util
open Lowering_state
open Base.Type_util
open Knot

(** [ret] of an effect monad, the global [use] (at [r]) applied to [a1 :: l],
    in expression position: the returned value in sequential mode, an
    [ITree<R>::ret] in reified mode. *)
let gen_return_expr cx (slot : Slot.slot) env ~r ~use ~a1 ~l : Cpp_ir.Lowered.Expr.t =
  let ret = slot.Slot.ret in
  let ret_tys = Base.Core_util.written_type_args use in
  if not (Monadic.is_sequential_effect cx Core_plan.Effects.Return use) then begin
    (* Reified mode: Ret produces ITree<R>::ret(value). Don't strip it. *)
    let t = Base.Common.last (a1 :: l) in
    match t with
    | Core.Expr.Global {callee = g; _} when is_ghost g ->
      Monadic.mk_itree_ret Void []
    | _ ->
      let inner = (gen_expr_typed cx (Slot.at ~ret ()) env t).expr in
      (* The result type is the type argument written for the variable the
         returned value is at: [Ret : forall E R, R -> itree E R].  One
         extraction could not read says nothing. *)
      let r_cpp =
        let value_var =
          match List.rev (Base.Type_util.core_value_domains (find_type r)) with
          | Core.Type.Variable {variable = j; _} :: _ -> Some j
          | _ -> None
        in
        match Option.bind value_var (Base.Core_util.Var_types.find_tvar ret_tys) with
        | Some r_core when not (Base.Core_util.is_erased_type r_core) -> Types.cpp_of_core cx env r_core
        | _ -> Void
      in
      Monadic.mk_itree_ret r_cpp [inner]
  end
  else begin
    let t = Base.Common.last (a1 :: l) in
    (gen_expr_typed cx (Slot.at ~ret ()) env t).expr
  end

(** [bind] of an effect monad in sequential mode, the application [a], in
    expression position: an immediately invoked lambda over the statements
    that sequence it. *)
let gen_bind_expr cx (slot : Slot.slot) env (a : Core.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let ret = slot.Slot.ret in
  (* Sequential mode: bind in expression context (e.g., nested inside
     another expression). Wrap in IIFE so gen_stmts can sequentialize. *)
  with_escape_analysis cx ~ret (fun ret -> with_region cx ~ret a (fun () ->
    Match_types.value_iife cx env (Core_plan.Query.infer_core_body_type a) (fun into -> gen_stmts cx (Slot.at ~ret ()) env (Destination.Return into) a) ) )

(** [bind] of an effect monad, the global [use] (at [r]) applied to
    [a1 :: a2 :: l], in statement position ending in [k]: the action's
    statements, its result bound for the continuation in sequential mode, the
    [bind] call as an expression in reified mode. *)
let gen_bind_stmts cx (slot : Slot.slot) env (k : Destination.t) (ast : Core.Expr.t) ~r ~use ~a1 ~a2
  ~l : Cpp_ir.Lowered.Stmt.t list =
  let ret = slot.Slot.ret in
  let bind_tys = Base.Core_util.written_type_args use in
  (* The action's result type: the argument written for the variable the
     continuation takes, [A] in [bind : forall A B, M A -> (A -> M B) -> M
     B].  One extraction could not read ({!Rocq_to_core.Extraction.observe_type_arg}: a
     type constructor such as an HKT carrier) says nothing. *)
  let action_result_ty =
    match List.rev (Base.Type_util.core_value_domains (find_type r)) with
    | Core.Type.Arrow {parameter = Core.Type.Variable {variable = j; _}; _} :: _ -> (
      match Base.Core_util.Var_types.find_tvar bind_tys j with
      | Some t when not (Base.Core_util.is_erased_type t) -> Some t
      | _ -> None )
    | _ -> None
  in
  (* Reified mode: bind is a real function call, not desugared. *)
  if not (Monadic.is_sequential_effect cx Core_plan.Effects.Bind use) then
    Destination.finish_inlined cx k (Knot.gen_expr_typed cx (Slot.at ~ret ~slot ()) env ast)
  else begin
    (* Sequential mode: desugar bind into sequential statements. *)
    let a_core, f = Base.Common.last_two (a1 :: a2 :: l) in
    let action = Knot.gen_expr_typed cx (Slot.at ~ret ()) env a_core in
    (* Run in place, the action yields its result: the monad's last type
       argument. *)
    let rec value_type (t : Core.Type.t) =
      (* An action is no function: an arrow left is a type binder. *)
      match Base.Type_util.resolve_meta t with
      | Arrow {parameter; result} when Base.Core_util.is_erased_type parameter -> value_type result
      | t -> t
    in
    let action =
      match Option.map value_type (Typed_checks.core_type_of cx a_core) with
      | Some (Global_app {type_arguments = _ :: _ as args; _}) ->
        Cpp_ir.Typed.v ~ty:(Typed_checks.core_value_type cx env (Some (List.hd (List.rev args)))) action.expr
      | _ -> action
    in
    let a = action.expr in
    let ids', f = collect_lams f in
  let ids, env =
    push_vars'
      (List.map (fun (x, ty) -> (cpp_id_of_id (id_of_binder_name x), ty)) ids')
      env
  in
  Binders.push_binders cx env ids;
  let bound_by_bind env = core_binder cx ~site:(Binding (Core.Global_use.occurrence use)) env 1 in
  (* Where a machine resumes at the continuation's parameter, which of
     what its frame keeps the save moves is the plan's, as at a let. *)
  ( match (ids, Ownership_ir.Region.save_moves cx.ctx.lexical.move_plan (Core.Global_use.occurrence use)) with
  | _ :: _, Some moved -> Option.iter (fun b -> Ownership_ir.Region.Frame_save.record b moved) (bound_by_bind env)
  | _ -> () );
  (
  match ids with
  | (x, core_ty) :: _ ->
    let ty = Types.cpp_of_core cx env core_ty in
    if (match ty with Void | Obligation Unresolved_type -> true | _ -> false) || core_type_is_unit core_ty then
      (* Unit/void bind result: execute the action for side effects,
         then declare the variable as Unit::e_TT so the continuation
         can reference it if needed. *)
      let action_is_pure_ret =
        match a_core with
        | Core.Expr.Apply {callee = Core.Expr.Global use; _} -> Monadic.is_effect cx Core_plan.Effects.Return use
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
         and Ret-in-void optimization may drop Core-level references). *)
      let body = gen_stmts cx (Slot.at ~ret ~slot ()) env k f in
      let cpp_ty = Types.cpp_of_core cx env core_ty in
      let decl : Cpp_ir.Lowered.Stmt.t list =
        if not (Lifting.stmts_reference_var x body) then []
        else if core_type_is_unit core_ty && not (is_cpp_unit_type cpp_ty) then
          []
        else if core_type_is_unit core_ty then
          [Cpp_ir.Typed.bind ?binder:(bound_by_bind env) (x) (cpp_ty) (Monadic.mk_tt_expr ())]
        else
          []
      in
      side_effect @ decl @ body
    else begin
      match Cpp_build.extract_block_template a with
      | Some (ref, tmpl, args, tys) ->
        (Foreign_block
          { custom = ref;
            template = tmpl;
            result = x;
            result_type = ty;
            values = args;
            type_args = tys;
            binder = bound_by_bind env } : Cpp_ir.Lowered.Stmt.t)
        :: gen_stmts cx (Slot.at ~ret ~slot ()) env k f
      | None ->
        let body = gen_stmts cx (Slot.at ~ret ~slot ()) env k f in
        (* A variable the continuation returns as it is is declared at the
           type the function returns, where that is the same type written
           through an alias: [STArray node], not the [STArray (nat * nat)]
           the action's value was inferred at. *)
        let ty =
          match (ret, List.rev body) with
          | Some r, Return (Some (Local y | Move (Local y))) :: _ when Names.Id.equal x y ->
            let al = Coerce.aliases_in cx in
            (* the result an erased tree is written as, [%t1] *)
            let rec result (t : Cpp_ir.Lowered.Type.t) =
              match t with
              | Entity_application (g, xs, _) -> (
                match Option.bind (Base.Type_util.spelled_as_argument g) (List.nth_opt xs) with
                | Some t -> result t
                | None -> t )
              | t -> t
            in
            let r = result r in
            let r' = Coerce.normal al r and ty' = Coerce.normal al ty in
            if r <> ty && (r' = ty' || Base.Type_util.cpp_ty_eq r' ty') then r
            else ty
          | _ -> ty
        in
        Typed_checks.agreement cx ~site:"bind result" action (Exactly ty);
        (Cpp_ir.Typed.bind ?binder:(bound_by_bind env) (x) (ty) (a) : Cpp_ir.Lowered.Stmt.t) :: body
    end
  | _ ->
    (* No lambda parameters (eta-reduced continuation like bare Ret).
       Execute the action for side effects, then run the continuation. *)
    let side_effect : Cpp_ir.Lowered.Stmt.t list =
      match a with Enum_value _ -> [] | _ -> [Expression a]
    in
    ( match f with
    | Core.Expr.Global use when Monadic.is_effect cx Core_plan.Effects.Return use ->
      (* Eta-reduced Ret: bind action Ret = action (monad right identity).
         In sequential mode, just execute the action and return. *)
      if (ret = Some Cpp_ir.Type.Void) then
        side_effect @ [(Return None : Cpp_ir.Lowered.Stmt.t)]
      else
        [Destination.finish cx k action]
    | _ ->
      (* Eta-reduced non-Ret continuation: f is a bare function reference.
         Bind action result to a temp var and apply f to it, instead of
         discarding the result and returning f unapplied. *)
      let non_void_ty =
        match action_result_ty with
        | Some ty ->
          let cpp_ty =
            Types.cpp_of_core cx env ty
          in
          if cpp_ty = Void || cpp_ty = Obligation Unresolved_type || core_type_is_unit ty then
            None
          else
            Some (cpp_ty, Ownership_ir.Region.worth_moving ty)
        | None -> None
      in
      ( match non_void_ty with
      | Some (cpp_ty, worth_moving) ->
        let temp_id = Id.of_string "_bind_result" in
        let f_typed = Knot.gen_expr_typed cx (Slot.at ~ret ()) env f in
        (* The continuation is the temporary's one reader. *)
        let result : Cpp_ir.Lowered.Expr.t = if worth_moving then Move (Local temp_id) else Local temp_id in
        let app = Cpp_ir.Build.call f_typed.expr [result] in
        Typed_checks.agreement cx ~site:"bind temporary" action (Exactly cpp_ty);
        [ Cpp_ir.Typed.bind (temp_id) (cpp_ty) (a);
          Destination.finish cx k
            (Cpp_ir.Typed.v ~ty:(Option.default Cpp_ir.Typed.unannotated (Cpp_ir.Typed.applied f_typed.ty 1)) app) ]
      | None ->
        side_effect @ gen_stmts cx (Slot.at ~ret ~slot ()) env k f ) ) )
  end

(** [ret] of an effect monad, [use] applied to [a1 :: l], in statement
    position ending in [k]: [k] of the returned value (a bare [return;] in a
    function returning [void]) in sequential mode, [k] of the whole term
    lowered as an [ITree<R>::ret] in reified mode. *)
let gen_return_stmts cx (slot : Slot.slot) env (k : Destination.t) (ast : Core.Expr.t) ~use ~a1 ~l :
  Cpp_ir.Lowered.Stmt.t list =
  let ret = slot.Slot.ret in
  if not (Monadic.is_sequential_effect cx Core_plan.Effects.Return use) then begin
    (* Reified mode: Ret is a constructor call, not desugared. *)
    Destination.finish_inlined cx k (Knot.gen_expr_typed cx (Slot.at ~ret ~slot ()) env ast)
  end
  else begin
    (* Sequential mode: eliminate Ret, just use the value. *)
    let t = Base.Common.last (a1 :: l) in
    if (ret = Some Cpp_ir.Type.Void) then
      (* Void-returning function: discard the value and return. *)
      [Return None]
    else
      [Destination.finish cx k (Knot.gen_expr_typed cx (Slot.at ~ret ?expected_ty:(ret) ()) env t)]
  end
