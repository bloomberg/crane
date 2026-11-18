(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Lambdas lowered to C++ closures: which binders become parameters, what
    the closure captures and by which mode, how it passes its parameters,
    and the return type it is written against.  One of the modules lowering Core
    bodies to CppIR that {!Lower_expr} drives; it calls back into
    expression and statement lowering through {!Knot}. *)

open Base.Common
open Names
open Base.Core_util
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query
open Knot

module IntSet = Core_plan.Escape.IntSet

(** The names of the variables at the de Bruijn indices [is] a closure
   captures, in the order a capture list spells them; a class instance is a
   template parameter, not a value it captures. *)
let capture_names env is =
  List.sort_uniq Id.compare
    (List.filter
       (fun id -> not (Base.Common.is_tc_instance_id id))
       (List.filter_map (fun i -> Base.Common.get_db_name_opt i env) is) )

(** The names of the variables [captures] says a closure takes by move. *)
let moved_names env captures =
  capture_names env (List.filter_map (function i, Ownership_ir.Region.Capture.By_move -> Some i | _ -> None) captures)

(** A local fixpoint's wrapper parameter, of Core type [ty], forwarded to the
   impl: its one read, a move where the wrapper takes it by value. *)
let forwarded ~by_value ty (v : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  if by_value && Ownership_ir.Region.worth_moving ty && not (core_type_is_unit ty) then Move v else v

(** Whether a lambda generated as [passing] says owns each parameter it
   takes, innermost first, as its parameters are listed. *)
let owned_flags passing = List.rev_map (fun p -> p = Core_plan.Callable_abi.Owned) (List.filter_map Fun.id passing)

(** The lambda [a] as a C++ closure, written against [expected_ty] where the
    position states a function type: its binders split where the expected
    type returns a function, the parameters it takes and how, its captures,
    and its body as statements returning its result. *)
let gen_lambda cx ~expected_ty ~slot env (a : Core.Expr.t) : Cpp_ir.Lowered.Expr.t =
  (* What the lambda takes by move as it is made. *)
  let moved_captures = moved_names env (Ownership_ir.Region.captures cx.ctx.lexical.move_plan a) in
  (* Whether a binder becomes a C++ parameter: see
     {!Lambda_params.lambda_binder_emitted}. *)
  let binder_emitted ~body binders i ty =
    Lambda_params.lambda_binder_emitted cx env ~expected_ty ~body binders i ty
  in
  (* A slot spelled [std::type_identity_t<Id_<...>>] -- a definitional
     class, taken out of deduction -- is still a function type, and the
     lambda is written against it: its arity and its result. *)
  let expected_ty =
    let rec as_fun (t : Cpp_ir.Lowered.Type.t) =
      match t with
      | Non_deduced t' -> as_fun t'
      | Const t' | Reference (Lvalue, t') -> as_fun t'
      | Function _ -> Some t
      | t -> (
        match Types.unfold_cpp_typedef cx env t with
        | Function _ as f when f <> t -> Some f
        | _ -> None )
    in
    match expected_ty with
    | Some t -> ( match as_fun t with Some f -> Some f | None -> expected_ty )
    | None -> None
  in
  let args, a = collect_lams a in
  (* Nested binders normally flatten into one multi-parameter C++ lambda.
     That is wrong when the context expects a curried function whose result
     is itself a function -- e.g. an [endo (nat -> nat)] field of type
     [std::function<F(F)>] with [F = std::function<uint64_t(uint64_t)>].
     Keep only the binders the expected type takes and let the remainder
     become the closure it returns. *)
  let args, a =
    (* An alias for a function type -- a codomain [cont R A] -- is one the
       lambda has to return as much as a spelled-out [std::function]. *)
    let rec fun_ty_of (t : Cpp_ir.Lowered.Type.t) =
      match t with
      | Const t | Reference (_, t) -> fun_ty_of t
      | Function (dom, cod) -> Some (List.length dom, cod)
      | t -> (
        match Types.unfold_cpp_typedef cx env t with
        | Function _ as f when f <> t -> fun_ty_of f
        | _ -> None )
    in
    let is_runtime_binder (_, ty) = is_runtime_binder_type ty in
    let split_after_runtime n binders =
      (* Prefix of [binders] holding exactly [n] runtime binders, or [None]
         if there are no more than [n] of them. *)
      let rec go seen acc = function
        | [] -> None
        | b :: rest ->
          let seen = if is_runtime_binder b then seen + 1 else seen in
          if seen > n then Some (List.rev acc, b :: rest)
          else go seen (b :: acc) rest
      in
      go 0 [] binders
    in
    (* Binders the expected type takes that the term does not write: the
       body is a function value, and the context wants its parameters in
       this lambda's own list rather than in a closure it returns.  Under-
       applied calls are eta-expanded too, but at the C++ level and after
       this lambda has been built, so the synthesised parameter lands
       {e inside} it -- [pair -> (list -> list)] where the consumer takes
       [(pair, list) -> list].  Writing the missing binders here instead
       makes the body a saturated call, so that expansion never fires.

       The binders are given no Core type on purpose: the derivation below
       reads an erased parameter's type out of [expected_ty]'s domain at
       the same index, which is the only place that says what it is. *)
    (* [extend n] -- the binders the expected signature takes that the term
       does not write, or [None] where there are none worth writing.

       Each test below has to run only once the ones before it have passed:
       the count decides whether anything is missing at all, and the later
       ones index the last [k] domains, which is not a meaningful range
       until [k] is known to be positive.  Written as nested [if]s rather
       than one condition for that reason -- OCaml's [let] is strict, so a
       guard placed after the computation it guards never runs. *)
    let extend n =
      (* Count the binders that will be {e emitted}, on the same terms the
         parameter list below is filtered: a binder whose recorded type is
         dummy is still a parameter where the body names it. *)
      let emitted_binder i (_, ty) = binder_emitted ~body:a args i ty in
      let k =
        n - List.length (List.filteri (fun i b -> emitted_binder i b) args)
      in
      if k < 0 then
        (* The term writes {e more} binders than the signature declares.
           Nothing is missing, and the surplus is not this function's
           business: a slot typed [std::function<T(U)>] against a
           two-binder lambda is an ordinary curried result, which the
           [split_after_runtime] branch above handles where the codomain
           says so. *)
        None
      else if k = 0 then None
      else if
        (* The expected C++ arity has to be backed by the same number of Core
           domains that genuinely carry a value.  A reified tree's
           continuation is typed [unit -> itree ...] and takes one
           [std::monostate]: the value carries nothing but the slot is real,
           so the binder counts like any other. *)
        let real ty = is_runtime_binder ((), ty) in
        let rec leading i ty =
          i = 0
          ||
          match resolve_meta ty with
          | Core.Type.Arrow {parameter = a; result = b} -> real a && leading (i - 1) b
          | _ -> false
        in
        not (match slot.Slot.expected_core_ty with Some ty -> leading n ty | None -> false)
      then None
      else if
        (* A binder is only worth writing if the slot says what it is.  The
           synthesised ones are the last [k] of the expected signature's
           domains, and each has to be a type this lambda could be written
           against: spelled with no erased position anywhere in it, and
           naming no type variable out of scope here (the same condition
           {!slot_param_cpp_ty} imposes, and for the same reason).  Where it
           is not, the parameter would be declared [const auto &] or
           [std::any] -- an untyped parameter the consumer cannot resolve,
           which is worse than the closure the term already returns, and
           which would also displace the C++-level expansions that do have
           types to work from. *)
        not
          ( match Option.map (Types.unfold_cpp_typedef cx env) expected_ty with
          | Some (Function (doms, _)) when List.length doms = n ->
            let tvars = get_current_type_vars cx in
            List.for_all
              (fun i ->
                match List.nth_opt doms i with
                | Some t ->
                  (not (Base.Type_util.has_tany_written t))
                  && Id.Set.for_all
                       (fun nm -> List.exists (Id.equal nm) tvars)
                       (Cpp_ir.Types.variable_names t)
                | None -> false )
              (List.init k (fun i -> n - k + i))
          | _ -> false )
      then None
      else
        let fresh =
          List.init k (fun i ->
              ( Core.Binder_name.Generated (Id.of_string (Printf.sprintf "_eta%d" (k - 1 - i))),
                Core.Type.Unknown ) )
        in
        (* The body applied to the binders, [rels] their indices where it
           stands, taken in where the body makes the closure the call would
           apply, so that no closure is built at every call: into a let's
           body, a lambda's parameter, and the arguments of a local
           function applied to fewer than it takes. *)
        let rec applied (a : Core.Expr.t) rels =
          match (a, rels) with
          | _, [] -> a
          | Core.Expr.Apply {callee = Core.Expr.Bound_variable _ as f; arguments}, _ ->
            Core.Expr.Apply {callee = f; arguments = arguments @ List.map Core.Expr.fresh_rel rels}
          | Core.Expr.Let l, _ -> Core.Expr.Let {l with body = applied l.body (List.map succ rels)}
          | Core.Expr.Lambda {body; _}, r :: rest ->
            applied (Base.Core_util.ast_subst_each (fun () -> Core.Expr.fresh_rel r) body) rest
          | a, _ -> Core_passes.Spines.apply a (List.map Core.Expr.fresh_rel rels)
        in
        Some (fresh @ args, applied (ast_lift k a) (List.init k (fun i -> k - i)))
    in
    match Option.bind expected_ty fun_ty_of with
    | Some (n, cod) when n > 0 && fun_ty_of cod <> None ->
      (* [collect_lams] yields binders innermost-first; the ones to keep are
         the outermost [n]. *)
      ( match split_after_runtime n (List.rev args) with
      | Some (kept, inner) ->
        ( List.rev kept,
          List.fold_left
            (fun b (x, ty) -> Core.Expr.Lambda {parameter = x; parameter_type = ty; body = b})
            a (List.rev inner) )
      | None -> ( match extend n with Some r -> r | None -> (args, a) ) )
    | Some (n, _) when n > 0 -> (
      match extend n with Some r -> r | None -> (args, a) )
    | _ -> (args, a)
  in
  (* The binders refined against the slot, where it is not a box: see
     {!Lambda_params.slot_refined_lambda}. *)
  let binders_left_open = List.exists (fun (_, ty) -> Lambda_params.has_open_meta ty) args in
  let args, a =
    Lambda_params.slot_refined_lambda cx env
      ~expected_core_ty:(if Slot.boxed slot then None else slot.Slot.expected_core_ty)
      args a
  in
  let lam_params = List.map (fun (x, y) -> (id_of_binder_name x, y)) args in
  let args, env = push_vars' lam_params env in
  let saved_env_types = cx.ctx.lexical.env_types in
  Binders.push_binders cx env args;
  (* Infer owned/borrowed for each lambda parameter using escape analysis.

     Owned parameters (stored in a data structure or returned) are passed by
     value (shared_ptr<T>), transferring ownership to the callee.  Borrowed
     parameters (only read, not stored/returned) are passed by const ref
     (const shared_ptr<T>&), avoiding a refcount bump on every call.

     The inference is conservative: if a parameter escapes in any code path
     (e.g. captured by a closure, stored in a constructor, or returned), it
     is marked as owned.  See {!Core_plan.Escape.infer_owned_params}. *)
  let n_all_params = List.length lam_params in
  let owned_flags = Ownership.infer_owned_flags cx a args
  in
  let args_with_owned =
    List.map2 (fun (id, ty) owned -> (id, ty, owned)) args owned_flags
  in
  (* A binder typed [Core.Type.Erased] carries nothing, so it is not a C++ parameter.
     Unless the body names it: an
     instance method's body is read at the class's erased method type, where
     a value binder the class quantified over has no type left to record,
     and dropping it leaves the body naming a variable nothing declares.
     What the body does with a binder settles whether it is one; the
     recorded type only says so where there is nothing to go on. *)
  (* A reified tree's continuation is typed [unit -> itree ...] and its
     consumer invokes it with one [std::monostate], so the slot is real even
     though the value carries nothing.  For a named function the signature is
     written from the type and the parameter is there whether or not a binder
     was; a lambda's parameter list {e is} its binder list, so dropping the
     binder drops the parameter and the callable comes out nullary.  A
     reified [unit] binder is therefore kept -- as an ordinary unused
     parameter -- and only the genuinely absent types are filtered. *)
  let filtered_args_with_owned =
    List.filteri
      (fun i (_, ty, _) -> binder_emitted ~body:a args_with_owned i ty)
      args_with_owned
  in
  (* Each emitted binder's position among all of them, for the body's
     de Bruijn indices. *)
  let emitted_binder_indices =
    List.filteri
      (fun i _ ->
        let _, ty, _ = List.nth args_with_owned i in
        binder_emitted ~body:a args_with_owned i ty )
      (List.mapi (fun i _ -> i) args_with_owned)
  in
  let filtered_args =
    List.map (fun (id, ty, _) -> (id, ty)) filtered_args_with_owned
  in
  (* A lambda standing for a rank-2 argument -- [fun _ e => ...] for a
     parameter of type [forall X, E X -> M X] -- is handed a type the caller
     has not chosen yet.  Extraction leaves that type as [Core.Type.Unknown], which
     prints as [std::any], and a lambda written against [std::any] is a
     claim the body cannot keep: it would have to name a concrete result
     where only the caller knows one.

     The honest spelling is a polymorphic function object: the erased
     positions become the lambda's own template parameter, so the parameter
     reads [const E<_X> &] and the body says [_X] where it would otherwise
     guess.  The callee recovers the result with [std::invoke_result_t]; see
     {!Core_plan.Plan_templates.relax_tt_applied_return}. *)
  let rank2_carrier =
    (* Only where the slot deduces the callback's type.  A slot that spells
       its own signature -- a [std::function<Nat(std::any)>] field, say --
       has already settled what the lambda is, and a polymorphic function
       object does not convert to it. *)
    let slot_declares_signature =
      match Option.map (Types.unfold_cpp_typedef cx env) expected_ty with
      | Some (Function _) -> true
      | _ -> false
    in
    if
      (not slot_declares_signature)
      && List.exists
           (fun (_, ty, _) -> Rank2.quantifies_erased_type ty)
           filtered_args_with_owned
    then Some Rank2.carrier_name
    else None
  in
  (* {!Rank2.at_carrier} over the types inside the body's CppIR
     statements. *)
  let at_carrier (ty : Cpp_ir.Lowered.Type.t) =
    match rank2_carrier with
    | None -> ty
    | Some x ->
      Cpp_ir.Types.map
        (fun (t : Cpp_ir.Lowered.Type.t) ->
          match t with Obligation Opaque_type | Any -> Variable (Named x) | t -> t )
        ty
  in
  let f =
    with_escape_analysis cx (fun () ->
      let tvars = get_current_type_vars cx in
      (* What the slot this lambda flows into declares its parameters to be,
         when it declares a signature at all. *)
      let expected_param_cpp_tys =
        match Option.map (Types.unfold_cpp_typedef cx env) expected_ty with
        | Some (Function (doms, _)) -> Some doms
        | _ -> None
      in
      (* [filtered_args_with_owned] is innermost-first and the printer
         reverses it, while a slot's domain list is in source order, so a
         parameter's index into the two runs opposite ways. *)
      let n_emitted_params = List.length filtered_args_with_owned in
      let slot_dom j = n_emitted_params - 1 - j in
      let slot_dom_cpp_ty j =
        Option.bind expected_param_cpp_tys (fun doms ->
            List.nth_opt doms (slot_dom j) )
      in
      let cpp_arg_info =
        List.mapi
          (fun j ((id, _, _) as arg) ->
            let unused =
              match List.nth_opt emitted_binder_indices j with
              | Some i -> not (Base.Core_util.ast_occurs (i + 1) a)
              | None -> false
            in
            let param_cpp_ty, body_subst =
              Lambda_params.lambda_param_cpp_type cx env ~ns:cx.ctx.input.method_self_ns ~tvars
                ~rank2_carrier
                ~reified:(cx.ctx.input.itree_mode = Reified) ~n_params:n_all_params ~body:a ~unused
                ~slot_dom:(slot_dom_cpp_ty j) arg
            in
            (param_cpp_ty, Some id, body_subst) )
          filtered_args_with_owned
      in
      (* A binder the body never uses is a parameter with no name: named,
         it would be unused -- a [trigger Inc ;; k] continuation's [unit] --
         and could shadow a name the body introduces.  One kept only for the
         slot ({!binder_emitted}) is the common case. *)
      let arity_only =
        List.filteri
          (fun i _ -> not (Base.Core_util.ast_occurs (i + 1) a))
          args_with_owned
        |> List.map (fun (id, _, _) -> id)
      in
      let cpp_args =
        List.map2
          (fun (ty, id, _) (orig, _, _) ->
            (ty, if List.exists (( == ) orig) arity_only then None else id) )
          cpp_arg_info filtered_args_with_owned
      in
      (* The body owns the parameters the lambda declares by value, as a
         function's does. *)
      let lambda_owned =
        let declared i =
          let rec position j = function
            | [] -> None
            | i' :: rest -> if i' = i then Some j else position (j + 1) rest
          in
          Option.map (fun j -> let ty, _, _ = List.nth cpp_arg_info j in ty)
            (position 0 emitted_binder_indices)
        in
        Ownership.owned_parameters (List.length args_with_owned)
          ~owned:(fun i ->
            match declared i with Some ty -> not (Ownership.declared_by_reference ty) | None -> false )
          ~declared
          ~ty:(fun i -> let _, ty, _ = List.nth args_with_owned i in ty)
      in
      (* A template parameter C++ cannot deduce is worse than the erasure
         it replaces, so the function object is polymorphic only where the
         carrier reaches a parameter: an erased position the body alone
         mentions stays [std::any].  {!Cpp_build.mk_lambda} is what enforces that;
         asking it here keeps the body's generation in step with the
         signature it will be given. *)
      let carrier =
        match rank2_carrier with
        | Some x when List.exists (Cpp_ir.Types.exists (Cpp_ir.Type.is_variable_named x)) (List.map fst cpp_args) ->
          Some x
        | _ -> None
      in
      (* The parameters' declared C++ types are only known here, after
         [cpp_arg_info]; correct the assignment made when their scope was
         opened above so the body reads what the signature says.  A
         parameter dropped by [filtered_args_with_owned] keeps its
         conversion-derived assignment. *)
      let () =
        let declared =
          List.combine
            (List.mapi (fun j (id, core_ty, _) -> (j, (id, core_ty)))
               filtered_args_with_owned )
            cpp_arg_info
          |> List.map (fun ((j, (id, core_ty)), (ty, _, _)) ->
               (id, Lambda_params.lambda_param_assigned ~slot_dom:(slot_dom_cpp_ty j) core_ty ty))
        in
        Binders.assign_binder_types cx env
          ~cpp:(List.map (fun (id, _) -> List.assoc_opt id declared) args)
          args
      in
      let body_expected_core_ty =
        let rec strip_arrows n ty =
          if n = 0 then Some ty
          else match resolve_meta ty with
               | Core.Type.Arrow {result = cod; _} -> strip_arrows (n - 1) cod
               | _ -> None
        in
        (match slot.Slot.expected_core_ty with
        | Some fn_ty ->
          (match strip_arrows n_all_params fn_ty with
          | Some cod ->
            (match resolve_meta cod with
            | Core.Type.Erased _ | Core.Type.Unknown
            | Core.Type.Meta {contents = None} | Core.Type.Open _ -> slot.Slot.expected_core_ty
            | _ -> Some cod)
          | None -> slot.Slot.expected_core_ty)
        | None -> None)
      in
      (* Generate the body, then check if the body returns a lambda (this
         happens when extract_cons_app generates curried partial constructor
         applications with an [Core.Expr.Lambda_group_barrier] barrier). If so, convert the returned
         lambda to capture by value to avoid dangling references to the outer
         lambda's parameters. *)
      (* A lambda stored into an erased slot IS the value in that slot, so
         what it returns is erased too and its body inherits the [Boxed] slot. *)
      (* A [return] inside this lambda returns from the lambda, not from the
         enclosing function, so the body must not inherit the enclosing
         function's return type.  The slot this lambda flows into is the only
         thing that can say what the body returns.
         When the slot declares no signature at all -- a deduced [F0 &&]
         callback parameter, say -- there is nothing better to say, so the
         context is left alone.  A [void] codomain says nothing either: a
         unit-returning lambda spells its result [std::monostate] or nothing
         at all depending on what consumes it, which is a decision for the
         body's own generation. *)
      (* Every binder is a type or a proof: no lambda is emitted, the body is
         the value the slot takes, and it returns the slot's type itself --
         an absurd case under [fun (e : p = q) => ...] passed where a [nat]
         is wanted throws from a [uint64_t] thunk. *)
      let binderless_result =
        match (filtered_args, carrier, Option.map (Types.unfold_cpp_typedef cx env) expected_ty) with
        | [], None, Some t when t <> Void -> Some t
        | _ -> None
      in
      let with_lam_return_type f =
        match Option.map (Types.unfold_cpp_typedef cx env) expected_ty with
        | _ when binderless_result <> None -> with_cpp_return_type cx binderless_result f
        | _ when carrier <> None ->
          (* A polymorphic function object returns at the type its own
             parameter fixes, so the enclosing function's return type is
             not merely unhelpful here -- it is the wrong answer, and the
             body would spell it in place of the carrier.  What the body
             does return is the lambda's own Core codomain read at the
             carrier: the rank-2 variable is erased in that type, and the
             carrier is the name the parameter gave it back. *)
          let ret =
            match (body_expected_core_ty, rank2_carrier) with
            | Some core_ty, Some x ->
              Some (Rank2.at_carrier x (Types.cpp_ir_of_core_type cx env (get_current_type_vars cx)
                core_ty))
            | Some core_ty, None -> Some (Types.cpp_ir_of_core_type cx env (get_current_type_vars
              cx) core_ty)
            | None, _ -> None
          in
          with_cpp_return_type cx ret f
        | Some (Function (_, cod)) when cod <> Void ->
          (* Read in this scope: a variable of the callee's the slot names
             ([tfmap]'s [T2]) is erased where it sits, as the binders'
             types are, so what the body builds is what the slot reads. *)
          let scope = current_scope_type_names cx in
          let cod =
            if not binders_left_open then cod
            else
            Cpp_ir.Types.map
              (fun (t : Cpp_ir.Lowered.Type.t) ->
                match t with
                | Variable tv ->
                  let id = Cpp_ir.Type.variable_spelled tv in
                  if List.exists (Id.equal id) scope then t else Any
                | t -> t )
              cod
          in
          with_cpp_return_type cx (Some cod) f
        | _ -> f ()
      in
      let body_stmts =
        (match carrier with
         | None -> (fun f -> f ())
         | Some _ -> with_rank2_carrier cx carrier)
          (fun () ->
            with_lam_return_type (fun () ->
              with_region cx ~owned:lambda_owned a (fun () ->
                gen_stmts cx
                  ~slot:{slot with Slot.expected_core_ty = body_expected_core_ty}
                  env
                  (fun x : Cpp_ir.Lowered.Stmt.t -> Return (Some x))
                  a ) ) )
      in
      let body_stmts =
        List.fold_left
          (fun stmts (_, _, subst) ->
            match subst with
            | Some (id, expr) -> List.map (Lifting.local_var_subst_stmt id expr) stmts
            | None -> stmts )
          body_stmts cpp_arg_info
      in
      let body_stmts =
        Lambda_params.return_captures_by_value body_stmts
      in
      (* When the lambda body is a standalone fixpoint (Core.Expr.Fixpoint with no
         applied args), the fix represents a function value that would make
         this lambda curried — e.g. [fun x => fix f r := ...] generates
         [[=](x){auto f=...; return f;}] (1-arg returning fn) instead of
         the flat [[=](x,r){auto f=...; return f(r);}] (2-arg).  Fold the
         fix's own params into this lambda so the result is uncurried and
         directly compatible with [std::function<R(A,B)>] contexts. *)
      let cpp_args, body_stmts =
        match a with
        | Core.Expr.Fixpoint fix_group | Core.Expr.Cofixpoint fix_group when List.length filtered_args <= 1 ->
          let fix_lam_params, _ = Base.Core_util.collect_lams (Core.Recursion.Group.selected_member fix_group).body in
          let fix_value_params =
            List.filter
              (fun (_, ty) -> is_runtime_binder_type ty)
              fix_lam_params
          in
          ( match fix_value_params with
          | [] -> (cpp_args, body_stmts)
          | _ ->
            (* Only fold when body_stmts ends with a bare variable return,
               i.e. the non-lifted ycomb path.  Lifted (polymorphic) fixes
               are returned via a call expression and don't need folding. *)
            let last_is_var_return =
              match List.rev body_stmts with
              | Cpp_ir.Stmt.Return (Some (Local _)) :: _ -> true
              | _ -> false
            in
            if not last_is_var_return then (cpp_args, body_stmts)
            else
              let extra_cpp_params =
                List.mapi
                  (fun i (_, core_ty) ->
                    let bare =
                      Types.cpp_of_core cx env core_ty
                    in
                    let param_ty : Cpp_ir.Lowered.Type.t =
                      match bare with
                      | Shared_pointer _ ->
                        Reference (Lvalue, Const bare)
                      | _ -> bare
                    in
                    (param_ty,
                     Some (Id.of_string (Printf.sprintf "_fea%d" i))) )
                  fix_value_params
              in
              let extra_args =
                List.map
                  (fun (_, id_opt) : Cpp_ir.Lowered.Expr.t -> Local (Option.get id_opt))
                  extra_cpp_params
              in
              let rec modify_last_return : Cpp_ir.Lowered.Stmt.t list -> Cpp_ir.Lowered.Stmt.t list = function
                | [] -> []
                | [Return (Some e)] ->
                  [Return (Some (Cpp_ir.Build.call e extra_args))]
                | stmt :: rest -> stmt :: modify_last_return rest
              in
              (* The printer does List.rev on params, so put extra params
                 first (they will print last, after the outer lambda's own
                 params).  Within extra_cpp_params, reverse so that fix param
                 i prints at position i from the left (natural order). *)
              ( List.rev extra_cpp_params @ cpp_args,
                modify_last_return body_stmts ) )
        | _ -> (cpp_args, body_stmts)
      in
      (* The return type annotation is left as [None], for C++ to deduce.
         Annotating here caused regressions for inner lambdas whose bodies
         return further closures (the inferred type became
         [std::function<...>] instead of the plain return type). *)
      let body_stmts =
        match carrier with
        | None -> body_stmts
        | Some _ ->
          let rec st s = Cpp_ir.Map.stmt (children ()) s
          and ex e = Cpp_ir.Map.expr (children ()) e
          and children () = Cpp_ir.Map.make ~expr:ex ~stmt:st ~type_:at_carrier () in
          List.map st body_stmts
      in
      (* ... except where the body does nothing but throw: a deduced return
         type is [void] there, and no slot that asked for a value can take
         it.  The slot's own codomain is what the throw stands in for, so
         name that. *)
      (* ... and where the body is a match whose branches produce
         different instantiations -- a dependent match refines the lambda's
         erased type binder per branch ([Ret (inl 0)] at the index, [inr <$>
         ...] at [nat + nat]) -- a deduced return type is rejected.  The
         lambda's own result erases what the branches disagree on, and each
         converts to it. *)
      let rec join (a : Cpp_ir.Lowered.Type.t) (b : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
        if a = b then a
        else
          match (a, b) with
          | Entity_application (g, xs, es), Entity_application (g', ys, _)
            when GlobRef.CanOrd.equal g g' && List.length xs = List.length ys ->
            Entity_application (g, List.map2 join xs ys, es)
          | In_namespace (ns, x), In_namespace (_, y) -> In_namespace (ns, join x y)
          | _ -> Any
      in
      let rec leaf_rtys = function
        | Core.Expr.Match {branches = pv; _} ->
          List.concat_map
            (fun {Core.Match.Branch.result_type = rty; body = body; _} ->
              match body with
              | Core.Expr.Match _ | Core.Expr.Let _ -> leaf_rtys body
              | _ -> [rty] )
            (Array.to_list pv)
        | Core.Expr.Let {body = b; _} -> leaf_rtys b
        | _ -> []
      in
      let dropped_type_binder =
        List.exists (fun (_, ty, _) -> erased_by_extraction ty) args_with_owned
      in
      let branch_join =
        if not dropped_type_binder then None
        else
          match List.map (Types.cpp_of_core cx env) (leaf_rtys a) with
          | t :: (_ :: _ as rest) ->
            let j = List.fold_left join t rest in
            if Cpp_ir.Types.prints_as_any j || not (Types.names_only_scoped_tvars cx j) then None
            else Some j
          | _ -> None
      in
      (* Branches refined by an enclosing function's type binder may
         disagree just the same -- [memM_interp]'s [Load] branch builds at
         [nat], the other at the index [T2] -- and the annotations do not
         show it, being the case's.  With more than one leaf, the slot,
         where it states a result this scope can write, is what each
         converts to. *)
      let slot_result_on_disagreement () =
        match leaf_rtys a with
        | _ :: _ :: _ -> (
          match Option.map strip_cpp_ref_const expected_ty with
          | Some (Function (_, cod))
            when cod <> Void && (not (Cpp_ir.Types.prints_as_any cod))
                 && Types.names_only_scoped_tvars cx cod ->
            Some cod
          | _ -> None )
        | _ -> None
      in
      let ret_ann =
        match body_stmts with
        | [Throw _] | [Return (Some (Abort _))] -> (
          match (binderless_result, Option.map strip_cpp_ref_const expected_ty) with
          | (Some _ as t), _ -> t
          | None, Some (Function (_, cod)) when cod <> Void -> Some cod
          | _ -> None )
        | _ -> (
          match branch_join with
          | Some _ as j -> j
          | None -> (
            match slot_result_on_disagreement () with
            | Some _ as r -> r
            | None ->
              (* ... and where the body returns callables from more than one
                 [return], which have no common type to deduce. *)
              let core_ty = match body_expected_core_ty with Some _ as t -> t | None -> infer_core_body_type a in
              Option.bind core_ty (fun t ->
                match Match_types.iife_closure_return_at ~several:true cx env t body_stmts with
                | Some ty when Types.names_only_scoped_tvars cx ty -> Some ty
                | _ -> None ) ) )
      in
      match
        Cpp_build.mk_lambda ?tparams:(Option.map (fun x -> [x]) carrier) (List.rev cpp_args) ret_ann
          body_stmts ~capture:Stored
      with
      | Lambda l -> Cpp_ir.Expr.Lambda {l with moved = moved_captures}
      | f -> f )
  in
  restore_env_types cx saved_env_types;
  ( match filtered_args with
  | [] ->
    (* All lambda params are dummy (type abstractions). Skip the lambda
       wrapper and generate the body expression directly. However, when the
       body is a reference to a template function (detectable by having
       Core.Type.Erased-typed leading params in its Core type), we must wrap it in a
       generic forwarding lambda — C++ cannot pass overloaded or template
       function names as first-class values. *)
    ( match a with
    | Core.Expr.Global ({callee = r; _} as use) ->
      let tys_inner = Base.Core_util.written_type_args use in
      let core_ty =
        match callee_core_type cx r with
        | Some ty -> ty
        | None -> Core.Type.Unknown
      in
      let has_dummy_prefix t =
        match core_domains t with d :: _ -> erased_by_extraction d | [] -> false
      in
      let non_dummy_param_tys = core_value_domains core_ty in
      (* A callee taking no value parameter -- [base (A : Type) : nat] -- is
         a value, declared as one: nothing to forward. *)
      if has_dummy_prefix core_ty && non_dummy_param_tys <> [] then
        (* The function is a template that had type-level leading params. We
           need a forwarding lambda because C++ can't pass template function
           names as first-class values.

           To handle non-deducible template type params (like T2 that only
           appears in the return type), we use a C++20 template lambda with
           explicitly typed value parameters. This lets the compiler deduce
           type variables from the argument types, and we compute
           non-deducible tvars via std::invoke_result_t. *)
        let n = List.length non_dummy_param_tys in
        let is_unary_method = n = 1 && Lambda_params.is_methodified r in
        if is_unary_method then
          (* The function was methodified: it is spelled [x.f()], not [f(x)],
             so no forwarding lambda can name it.  Emit the plain reference
             and let the printer wrap it in the method-calling lambda it
             already builds for method values. *)
          gen_expr cx env a
        else
        let arg_ids = List.init n field_param_id in
        let arg_vars = List.map (fun id : Cpp_ir.Lowered.Expr.t -> Local id) arg_ids in
        (* Collect all tvars from the Core type *)
        let all_tvars_set =
          List.fold_left
            collect_tvars_set
            IntSet.empty
            (non_dummy_param_tys @ [core_ty])
        in
        let all_tvars = IntSet.elements all_tvars_set in
        (* Tvars deducible from non-function value params *)
        let value_param_tys =
          List.filter
            (fun t ->
              match t with
              | Core.Type.Arrow _ -> false
              | _ -> true )
            non_dummy_param_tys
        in
        let deducible_set =
          List.fold_left
            (fun acc t -> spelled_tvars_of acc t)
            IntSet.empty value_param_tys
        in
        let deducible_tvars = IntSet.elements deducible_set in
        let non_deducible_tvars =
          List.filter (fun i -> not (IntSet.mem i deducible_set)) all_tvars
        in
        (* The lambda's own type binders, named so the callee's variables
           do not read as the enclosing declaration's. *)
        let local_tvar i = Base.Generated_name.indexed "T" i in
        let local_tvars =
          List.init (List.fold_left max 0 all_tvars) (fun k -> local_tvar (k + 1))
        in
        let local_ty ty =
          Types.template_arg_of_core_type cx ~site:Cpp_ir.Types.Through_tvar env local_tvars ty
        in
        let local_var j : Cpp_ir.Lowered.Type.t = Variable (Index (j, Some (local_tvar j))) in
        (* A forwarding parameter, and the argument that forwards it. *)
        let forwarding : Cpp_ir.Lowered.Type.t = Reference (Forwarding, Auto) in
        let forward (x : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t = Forward (Type_of x, x) in
        (* What the callee returns once given its value arguments, in the
           lambda's own variables. *)
        let result_core = Base.Type_util.core_drop_arrows n core_ty in
        (* The lambda returns what the call does: its type where every
           variable in it is named, [decltype(auto)] -- the call's own
           answer -- where one is not. *)
        let lambda ?ret tparams (params : Cpp_ir.Lowered.Type.t list) call =
          let ret : Cpp_ir.Lowered.Type.t =
            match ret with
            | Some t
              when (not (Base.Type_util.has_unnamed_tvar t)) && not (Cpp_ir.Types.prints_as_any t)
              ->
              t
            | _ -> Decltype_auto
          in
          Cpp_build.mk_lambda ~tparams
            (List.map2 (fun ty id -> (ty, Some id)) params arg_ids)
            (Some ret) [Return (Some call)] ~capture:Stored
        in
        if non_deducible_tvars <> [] && not (IntSet.is_empty deducible_set)
        then
          (* A template lambda with typed value parameters, which deduce the
             variables they spell; the function-typed parameter is
             forwarding, and a variable only the result names is the type
             that parameter returns at the deduced ones. *)
          let params =
            List.map
              (function
                | Core.Type.Arrow _ -> forwarding
                | ty -> Reference (Lvalue, Const (local_ty ty)) )
              non_dummy_param_tys
          in
          let fwd_args =
            List.map2
              (fun x ty ->
                match ty with Core.Type.Arrow _ -> forward x | _ -> x )
              arg_vars non_dummy_param_tys
          in
          let invoke_result : Cpp_ir.Lowered.Type.t =
            External
              ( "std::invoke_result_t",
                Reference (Lvalue, Type_of (Local (List.hd arg_ids)))
                :: List.map (fun j -> Cpp_ir.Type.Reference (Lvalue, local_var j)) deducible_tvars )
          in
          let ty_args =
            Calls.written_at_variables cx r
              (List.map
                 (fun i -> (i, if IntSet.mem i deducible_set then local_var i else invoke_result))
                 (List.sort compare (deducible_tvars @ non_deducible_tvars)) )
          in
          let ret =
            Cpp_ir.Types.substitute
              (fun i -> if IntSet.mem i deducible_set then Some (local_var i) else Some invoke_result)
              (local_ty result_core)
          in
          lambda ~ret
            (List.map local_tvar deducible_tvars)
            params
            (Cpp_ir.Build.call (mk_cppglob r ty_args) fwd_args)
        else
          (* Simple forwarding.  A parameter whose type names no variable is
             written at it: a value stored behind [std::any] is then unboxed
             by [crane_erase_fn] at that type rather than handed on boxed.
             With no type argument given, the variables are this lambda's
             own type binders, which nothing outside instantiates: the
             consumer, erased too, hands the value over at [std::any] --
             [interp] calling a named handler [h] with an event.  Every
             variable is then written as the box it is, and a parameter
             that mentions one is read at that erased type. *)
          let own_index = Base.Core_util.Var_types.is_empty tys_inner && all_tvars <> [] in
          let at_own_index ty =
            Base.Type_util.resolve_tvars_to_any
              (Types.cpp_ir_of_core_type cx env [] ty)
          in
          let mentions_tvar ty =
            not (IntSet.is_empty (collect_tvars_set IntSet.empty ty))
          in
          let params =
            List.map
              (fun ty ->
                match ty with
                | Core.Type.Arrow _ -> forwarding
                | _ when IntSet.is_empty (spelled_tvars_of IntSet.empty ty) ->
                  Reference (Lvalue, Const (Types.cpp_ir_of_core_type cx env [] ty))
                | _ when own_index -> Reference (Lvalue, Const Auto)
                | _ -> forwarding )
              non_dummy_param_tys
          in
          let fwd_args =
            List.map2
              (fun x ty ->
                match ty with
                | Core.Type.Arrow _ -> forward x
                | _ when own_index && mentions_tvar ty ->
                  Convert (at_own_index ty, x)
                | _ -> forward x )
              arg_vars non_dummy_param_tys
          in
          (* The inner type arguments as C++ types, by variable. *)
          let inner_tvars = get_current_type_vars cx in
          let by_var =
            List.map
              (fun (v, ty) ->
                (Core.Scheme.Var.ordinal v, Types.cpp_ir_of_core_type cx env inner_tvars ty) )
              (Base.Core_util.Var_types.bindings tys_inner)
          in
          (* An erased argument is left to deduction -- unless nothing can
             deduce it: [h : getE ~> itree noE] quantifies an index the
             enum [getE] does not carry, and the consumer, which erased it
             too, takes the tree at [std::any].  With no argument given at
             all -- the index is this lambda's own type binder -- every
             variable is such a one, since none is deducible here. *)
          let by_var : (int * Cpp_ir.Lowered.Type.t) list =
            if own_index then
              List.init (List.fold_left max 0 all_tvars) (fun k -> (k + 1, Cpp_ir.Type.Any))
            else if non_deducible_tvars = [] then List.filter (fun (_, t) -> t <> Cpp_ir.Type.Any) by_var
            else if by_var = [] then List.map (fun i -> (i, Cpp_ir.Type.Any)) non_deducible_tvars
            else by_var
          in
          let ret =
            Cpp_ir.Types.substitute
              (fun i -> List.assoc_opt i by_var)
              (Types.cpp_ir_of_core_type cx env [] result_core)
          in
          lambda ~ret [] params
            (Cpp_ir.Build.call (mk_cppglob r (Calls.written_at_variables cx r by_var)) fwd_args)
      else
        (* Every binder was a type: the body is the value the slot takes. *)
        gen_expr cx ?expected_ty ~slot env a
    | _ ->
      (* Body is not a template function ref — wrap in void thunk (old
         behavior). gen_expr env a might produce lambdas with [&] capture
         which fail at static scope, so we use the pre-built capture-free
         lambda f.

         Exception: in reified mode, when the lambda had void-typed params
         (from monadic result type erasure), keep the lambda as a function
         object rather than an IIFE. This is needed for itree_bind
         continuations which expect std::function, not the result of
         calling the function. *)
      if cx.ctx.input.itree_mode = Reified
         && List.exists (fun (_, ty) -> core_type_is_unit_or_void ty) lam_params then
        f
      else
        Cpp_ir.Build.call f [] )
  | _ ->
    let core_arity =
      match slot.Slot.expected_core_ty with
      | Some ty -> count_core_value_arrows ty
      | None -> 0
    in
    (* Whether any branch of the lambda's own body returns a closure.  Only
       the statement structure is walked: a lambda nested inside some other
       expression is not this lambda's result. *)
    let returns_a_lambda =
      match f with
      | Lambda {body = body; _} ->
        let found = ref false in
        let rec walk (s : Cpp_ir.Lowered.Stmt.t) =
          ( match s with
          | Return (Some (Lambda _)) -> found := true
          | _ -> () );
          ignore
            (Cpp_ir.Map.stmt
               (Cpp_ir.Map.make ~expr:Fun.id ~stmt:(fun s -> walk s; s) ~type_:Fun.id ())
               s)
        in
        List.iter walk body;
        !found
      | _ -> false
    in
    Coerce.eta_expand_to_expected ?expected_ty ~core_arity ~returns_a_lambda
      ~arity:(List.length filtered_args) f )
