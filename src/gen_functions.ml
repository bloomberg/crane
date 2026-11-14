(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Type aliases and top-level functions and constants: the function head
    and body, declarations, and the generated-entity record a function's
    file views come from.

    Part of declaration generation (MiniML to CppIR): the declaration-level
    layer over the expression translation in {!Translation}, re-exported
    through {!Gen_decls}.  Translation still generates MiniCpp; a body is
    lowered into CppIR as it comes back, and every declaration here is
    CppIR.  The callable plan of each function ({!plan_function}) is
    made before any body is generated; generating the function reads it
    back ({!planned_relaxations}, {!declare_planned}). *)

open Common
open Miniml
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Translation
open Plan_templates
open Gen_context
open Gen_records

module IntSet = Escape.IntSet

(** The right-hand side of the type alias [r] over its parameters [vars],
    with the note that goes with it.  [ot] is [None] for a signature entry
    that names a type without defining it.  The three irregular right-hand
    sides -- a custom extraction's verbatim spelling, an axiom's [std::any]
    placeholder, and an absent definition -- are all expressed as
    {!Cpp_ir.Decl.Type_alias} fields rather than as a rendered string handed to the
    printer. *)
let type_alias_rhs r vars ot =
  with_method_ns_for_locals @@ fun () ->
  match Cpp_state.find_type_custom_opt r with
  | Some (_ids, s) -> (Some (External (s, []) : Cpp_ir.Lowered.Type.t), None)
  | None -> (
    match ot with
    | None -> (None, None)
    | Some Taxiom -> (Some Any, Some "AXIOM TO BE REALIZED")
    | Some t ->
      (* Name the body's type variables from the alias's own list.  Left
         anonymous they are resolved by position against the emitted
         parameters, and the promoted ones lead (they are defaulted, and a
         default may not precede a plain parameter) -- so [Definition Top :=
         itree TopE], eta-expanded to supply [itree]'s missing value
         parameter, read the value slot off the FRONT and wrote [ITree<iptr>].
         Eta-expansion appends; positional resolution reads from the
         beginning. *)
      (Some (cpp_ir_of_ml_type (empty_env ()) vars t), None) )

(** The kinds of the parameters [vars] of the type alias [r], whose body is
    [t], as {!gen_type_alias} declares them -- without recording them. *)
let type_alias_kinds r vars t =
  let vars = rename_tvars Cpp_state.keywords vars in
  let rhs, _ = type_alias_rhs r vars (Some t) in
  snd (template_kinds ?applied:rhs vars [t])

(** Build the [using] declaration for a type alias; see {!type_alias_rhs}. *)
let gen_type_alias r vars ot =
  let vars = rename_tvars Cpp_state.keywords vars in
  let du_rhs, du_note = type_alias_rhs r vars ot in
  let du_tparams_head =
    hkt_templates ?applied:du_rhs r vars
      (match ot with Some t -> [t] | None -> [])
  in
  let du_tparams =
    List.map (fun v -> (Cpp_ir.Template.Parameter_kind.Typename, v)) (Table.promoted_type_params r)
    @ du_tparams_head
  in
  (* A family parameter [hkt_templates] left plain is still written applied
     in the rendering; the applied family is the family's own struct. *)
  let du_rhs =
    let plain =
      List.filter_map
        (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) -> match tt with Template _ -> None | _ -> Some id)
        du_tparams
    in
    let in_scope = List.map snd du_tparams in
    Option.map
      (Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) ->
        match t with
        | Apply (head, args) when List.exists (fun id -> Plan_templates.head_tvar_is id head) plain ->
          Head_relaxation.rebind_plain_var_lowered ~in_scope head args
        | t -> t ))
      du_rhs
  in
  (Type_alias {type_params = du_tparams; name = r; rhs = du_rhs; note = du_note} : Cpp_ir.Lowered.Decl.t)

(** The occurrences of the uses of [n] in [b] written at another instance
    than [n]'s own: a use that solves one of [n]'s variables to a ground
    type, as a self-call written [f bool] inside [f] does
    ({!Extraction.extract_cst_app}).  Every other self-call is at [n]'s own
    variables -- [Identity], or a hole a pass left for inference. *)
let other_instance_self_calls n b =
  let rec ground = function
    | Miniml.Tarr (a, c) -> ground a && ground c
    | Miniml.Tglob (_, l, _) -> List.for_all ground l
    | Miniml.Tmeta {contents = Some t} -> ground t
    | Miniml.Tstring -> true
    | _ -> false
  in
  let elsewhere use =
    match Global_use.instantiation use with
    | None -> false
    | Some inst ->
      Scheme.Instantiation.exists
        (fun _ (s : Miniml.ml_type Scheme.slot) ->
          match s.solution with Scheme.Type t -> ground t | Scheme.Identity -> false )
        inst
  in
  let found = ref [] in
  let rec walk = function
    | MLglob use when GlobRef.UserOrd.equal (Global_use.callee use) n && elsewhere use ->
      found := Global_use.occurrence use :: !found
    | e -> Mlutil.ast_iter walk e
  in
  walk b;
  !found

(** Substitute the global [id] with [repl] in expressions and statements.

    Identity here is the {i user} name, not the canonical one
    {!Common.globref_equal} compares.  Every caller substitutes a declaration's own reference for a
    self-call, and what makes an occurrence a self-call is that it is printed at
    the name being declared -- a property of the user name, since that is the
    one the C++ spelling comes from.  Two references can share a canonical name
    and still be different C++ names: [Include M] inside a functor re-exports
    [M]'s fields as constants of the including module, so the forwarder's body
    and the forwarder itself agree canonically and differ in exactly the
    qualifier that keeps the call from being a call to itself.

    A call made of one of the Core uses [spare] names keeps its head: the
    use was written at another instance than the declaration's own
    ({!other_instance_self_calls}), and its template arguments are that
    instance's. *)
let rec glob_subst_expr_ir ?(spare = []) (id : GlobRef.t) (repl : Cpp_ir.Lowered.Expr.t)
    (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match e with
  | Entity (id', _, _) when GlobRef.UserOrd.equal id id' -> repl
  | Call (({occurrence = Some o; _} as cs), (Entity (id', _, _) as head), args)
    when GlobRef.UserOrd.equal id id' && List.exists (Miniml.Occurrence.equal o) spare ->
    Call (cs, head, List.map (glob_subst_expr_ir ~spare id repl) args)
  | _ -> Cpp_ir.Map.expr (glob_subst_map ~spare id repl) e

(** Statement-level case of {!glob_subst_expr_ir}. *)
and glob_subst_stmt_ir ?(spare = []) id repl (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
  Cpp_ir.Map.stmt (glob_subst_map ~spare id repl) s

and glob_subst_map ~spare id repl =
  Cpp_ir.Map.make ~expr:(glob_subst_expr_ir ~spare id repl) ~stmt:(glob_subst_stmt_ir ~spare id repl)
    ~type_:Fun.id ()

(** Substitute the local [id] with [repl] in expressions and statements.
    A lambda moving [id] into its captures moves the variable it is
    replaced by.  A method's receiver becoming [this] keeps its name there:
    the closure captures a copy of the object, which
    {!Gen_inductives.replace_this_in_lambdas} names.  Replaced by anything
    else, it captures nothing of that name. *)
let rec var_subst_expr_ir (id : Id.t) (repl : Cpp_ir.Lowered.Expr.t) (e : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  match e with
  | Local id' when Id.equal id id' -> repl
  | Lambda l when List.exists (Id.equal id) l.moved ->
    let moved =
      List.sort_uniq Id.compare
        (List.concat_map
           (fun x ->
             if not (Id.equal x id) then [x]
             else
               match repl with
               | Local y -> [y]
               | This | Dereference This -> [x]
               | _ -> [] )
           l.moved )
    in
    Cpp_ir.Map.expr (var_subst_map id repl) (Lambda {l with moved})
  | _ -> Cpp_ir.Map.expr (var_subst_map id repl) e

(** Statement-level case of {!var_subst_expr_ir}. *)
and var_subst_stmt_ir id repl (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
  Cpp_ir.Map.stmt (var_subst_map id repl) s

and var_subst_map id repl =
  Cpp_ir.Map.make ~expr:(var_subst_expr_ir id repl) ~stmt:(var_subst_stmt_ir id repl) ~type_:Fun.id ()

(** Substitute unnamed type variables with named ones based on a variable
    list: each unnamed variable [Ti] in [s] is named by the [i]th of
    [tvars].  Used when generating methods, to name [T1], [T2], ... by the
    struct's template parameters. *)
let tvar_subst_stmt_ir (tvars : Id.t list) (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
  let type_ =
    Cpp_ir.Types.map (fun (ty : Cpp_ir.Lowered.Type.t) ->
        match ty with
        | Variable (Index (i, None)) -> (
          try Variable (Index (i, Some (List.nth tvars (pred i)))) with Failure _ -> ty )
        | _ -> ty )
  in
  let rec expr e = Cpp_ir.Map.expr (m ()) e
  and stmt s = Cpp_ir.Map.stmt (m ()) s
  and m () = Cpp_ir.Map.make ~expr ~stmt ~type_ () in
  stmt s

(** [dead_unit_returns_to_abort_ir cod body] rewrites [return tt;] into a throw
    when the enclosing function does not return [unit].

    A dependent match can have branches that are impossible by typing, e.g.

    {v
      match v in vec _ m return match m with O => unit | S _ => nat end with
      | vnil => tt
      | vcons _ x _ => x
      end
    v}

    Extraction erases the dependency, so the [vnil] branch survives as a plain
    [tt] sitting in a function whose C++ return type is [uint64_t] — which does
    not compile.  The branch is unreachable, so emit the same throw used for
    other absurd cases.

    A nested lambda is traversed under its own declared return type, since a
    [tt] returned from a lambda that really does return [unit] is well-typed.
    So is one returned where the result is the box: a type a type-level
    function computes ([tuple (nats n)], [unit] at [0]) erases to it, and its
    [unit] branch is as reachable as any other. *)
let dead_unit_returns_to_abort_ir (cod : Cpp_ir.Lowered.Type.t) (body : Cpp_ir.Lowered.Stmt.t list) =
  let is_unit : Cpp_ir.Lowered.Type.t -> bool = function
    | Void -> true
    | Entity_application (r, _, _) | In_namespace (r, _) -> Table.is_unit_type r
    | _ -> false
  in
  let rec is_tt : Cpp_ir.Lowered.Expr.t -> bool = function
    | Entity (r, _, _) -> Table.is_tt_constructor r
    | Call (_, f, _) -> is_tt f
    | _ -> false
  in
  let rec fix_stmts ret_ty stmts =
    match ret_ty with
    | Some t when not (is_unit t || Translation_types.resolves_to_any_type_ir t) ->
      List.map (fix_stmt ret_ty) stmts
    | _ -> List.map (fix_stmt None) stmts
  and fix_stmt ret_ty (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
    match s with
    | Return (Some e) when ret_ty <> None && is_tt e ->
      Return (Some (Abort (Translation_support.dead_branch_message, match ret_ty with Some t -> t | None -> Any)))
    | _ -> Cpp_ir.Map.stmt (fix_map ret_ty) s
  and fix_expr ret_ty (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
    match e with
    | Lambda l -> Lambda {l with body = fix_stmts l.return_type l.body}
    | _ -> Cpp_ir.Map.expr (fix_map ret_ty) e
  and fix_map ret_ty = Cpp_ir.Map.make ~expr:(fix_expr ret_ty) ~stmt:(fix_stmt ret_ty) ~type_:Fun.id () in
  fix_stmts (Some cod) body

(** Adapt closures returned from a function whose return type is the erased
    [std::any] (e.g. the [nat -> nat] branch of a dependent
    [if b then nat else nat -> nat]).  Like {!box_for_any_slot} at
    argument and value-declaration positions, the callable must be stored in
    the canonical [std::function<std::any(std::any...)>] form that the
    application site recovers with an [any_cast].  Nested lambda bodies are
    left alone: their returns answer to their own return type. *)
let erase_returned_fn_values_ir (ret_ty : Cpp_ir.Lowered.Type.t) (body : Cpp_ir.Lowered.Stmt.t list) =
  if not (Translation_types.resolves_to_any_type_ir ret_ty) then body
  else
    let rec fix_stmt (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
      match s with
      | Return (Some (Lambda _ as e)) -> Return (Some (Erase_callable (Boxed_whole, e)))
      | _ -> Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:Fun.id ~stmt:fix_stmt ~type_:Fun.id ()) s
    in
    List.map fix_stmt body

(** The rewrites every generated function body takes at its C++ result type
    [cod], a free function's and a method's alike: a [tt] returned where the
    result is not [unit] is dead ({!dead_unit_returns_to_abort_ir}), and a
    closure returned where the result erased is stored in the canonical form
    its caller reads ({!erase_returned_fn_values_ir}). *)
let finish_fn_body_ir cod body = dead_unit_returns_to_abort_ir cod (erase_returned_fn_values_ir cod body)

(** {!Translation.return_captures_by_value} in CppIR. *)
let return_captures_by_value_ir (stmts : Cpp_ir.Lowered.Stmt.t list) =
  let closure (l : _ Cpp_ir.Expr.Lambda.t) : _ Cpp_ir.Expr.Lambda.t =
    match l.capture with
    | Runs_in_place ->
      Probe.violation "closure capture" (Pp.str "a lambda holding references into its frame is returned");
      {l with capture = Stored}
    | _ -> l
  in
  let rec by_value (l : _ Cpp_ir.Expr.Lambda.t) = closure {l with body = List.map stmt l.body}
  and expr (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
    match e with
    | Lambda l -> Lambda (by_value l)
    | Call (res, Lambda l, args) -> Call (res, Lambda {l with body = List.map stmt l.body}, List.map expr args)
    | Call (res, f, args) -> Call (res, expr f, List.map expr args)
    | Dereference e -> Dereference (expr e)
    | Move e -> Move (expr e)
    | Forward (ty, e) -> Forward (ty, expr e)
    | Aggregate a -> Aggregate {a with values = List.map expr a.values}
    | Local_aggregate a -> Local_aggregate {a with values = List.map expr a.values}
    | Binary (op, a, b) -> Binary (op, expr a, expr b)
    | Unary (op, e) -> Unary (op, expr e)
    | Access (Dot, e, id) -> Access (Dot, expr e, id)
    | Scope (e, id, []) -> Scope (expr e, id, [])
    | Member (e, id) -> Member (expr e, id)
    | Project (e, id, ty) -> Project (expr e, id, ty)
    | Access_call (Arrow, e, id, args) -> Access_call (Arrow, expr e, id, List.map expr args)
    | Any_cast (ty, e) -> Any_cast (ty, expr e)
    | e -> e
  and stmt (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t =
    match s with
    | Return (Some e) -> Return (Some (expr e))
    | Expression e -> Expression (expr e)
    | If i -> If {condition = expr i.condition; then_ = List.map stmt i.then_; else_ = List.map stmt i.else_}
    | Switch w ->
      Switch
        { w with
          scrutinee = expr w.scrutinee;
          branches = List.map (fun (id, body) -> (id, List.map stmt body)) w.branches;
          default = Option.map (List.map stmt) w.default }
    | Match (scrut, branches, default) ->
      Match
        ( {scrut with expr = expr scrut.expr},
          List.map (fun (br : _ Cpp_ir.Stmt.Match.branch) -> {br with body = List.map stmt br.body}) branches,
          Option.map (List.map stmt) default )
    | Custom_match c ->
      Custom_match
        { c with
          scrutinee = expr c.scrutinee;
          branches =
            List.map (fun (b : _ Cpp_ir.Stmt.Custom_match.branch) -> {b with body = List.map stmt b.body}) c.branches }
    | s -> s
  in
  List.map
    (fun (s : Cpp_ir.Lowered.Stmt.t) : Cpp_ir.Lowered.Stmt.t ->
      match s with
      | Return (Some (Lambda ({capture = Runs_in_place; _} as l))) -> Return (Some (Lambda (closure l)))
      | Return (Some e) -> Return (Some (expr e))
      | s -> s )
    stmts

(** [return ty::lazy_([=]() -> cod { return x; })]: the body's result [x], of
    C++ type [cod], suspended whole as the coinductive [ml_ret], whose type
    arguments [cpp_of] spells. *)
let suspend_whole ~cpp_of ~cod ml_ret x : Cpp_ir.Lowered.Stmt.t =
  match ml_ret with
  | Miniml.Tglob (r, args, _) ->
    Return
      (Some
         (Suspend
            ( Entity_application (r, List.map cpp_of args, []),
              Cpp_ir.Build.lambda [] (Some cod) [Return (Some x)] ~capture:Stored )))
  | _ -> CErrors.anomaly (Pp.str "suspend_whole: a coinductive result is a Tglob")

(** The C++ expression stating the witness held by a [sig]-typed parameter
    called [name], when it can be stated at all.  A transparently extracted
    [sig] {i is} its witness, so the parameter stands for it; one left as a
    struct carries the witness in the field its single constructor registered.
    Either way the predicates that reach here compare the witness numerically,
    so a witness that is not a C++ scalar has nothing to compare and the
    precondition can only be reported as a comment. *)
let sig_witness_expr name (ml_ty : ml_type) =
  match ml_ty with
  | Miniml.Tglob (r, (Miniml.Tglob (w, _, _) :: _), _)
    when Table.is_custom_scalar_ref w ->
    if Table.is_custom r then Some name
    else
      let cname =
        match r with
        | GlobRef.IndRef ind ->
          ctor_struct_name_of_ref ~fallback_idx:0
            (GlobRef.ConstructRef (ind, 1))
        | _ -> ""
      in
      Some
        (name ^ "." ^ Id.to_string (Common.lookup_ctor_field_name ~owner:r cname 0))
  | _ -> None

(** Run [f] in the itree extraction mode that [ty]'s codomain calls for,
    restoring the enclosing mode afterwards.  Reified mode preserves [itree E R]
    as [shared_ptr<ITree<R>>]; sequential mode erases it to [R].  A codomain
    with no monad leaves the mode alone.

    Must wrap type conversion as well as body generation: void-ification and
    {!Translation_support.reify_monadic_param_type_ir} both
    read the mode.  We detect reified by the monad template mentioning "ITree",
    e.g. ["std::shared_ptr<ITree<%t1>>"]. *)
let with_itree_mode_for ty f =
  match Ml_type_util.codomain_monad ty with
  | Some monad_ref -> with_itree_mode (Core_effects.mode_of_monad monad_ref) f
  | None -> f ()

(** A class-typed parameter is not a value in C++: the class is a concept, and
    the instance satisfying it is a type.  Such a parameter therefore leaves the
    value parameter list and becomes one of the function's own template
    parameters, named as an instance parameter is -- which is the name every use
    of it ([_tcI0::width()]) and every call site already spell.

    Returns the parameters with the class-typed ones renamed in place, so that
    de Bruijn indices still line up, together with what each takes as a template
    parameter: its kind (in CppIR), its name, the class it instantiates, and
    the name the Rocq binder had. *)
let promote_typeclass_params (params : (Id.t * ml_type) list) =
  let counter = ref 0 in
  let temps = ref [] in
  let params =
    List.map
      (fun (id, ty) ->
        match Core_query.parameter_role ty with
        | Value -> (id, ty)
        | Dictionary ->
          let i = !counter in
          counter := i + 1;
          let instance_name = tc_instance_id i in
          (* A unary concept can be written inline ([Params _tcI0]), so the
             compiler enforces it.  A multi-parameter concept cannot: its extra
             type arguments are not in scope where the template parameter is
             declared. *)
          let tt =
            match ty with
            | Miniml.Tglob _ as ty -> Option.get (concept_constraint_of_class_type ty)
            | _ ->
              (* Unreachable: [Table.is_typeclass_type] only holds of a
                 [Tglob]. *)
              CErrors.anomaly
                (Pp.str
                   "gen_decls: type-class instance parameter whose type is not \
                    a global reference")
          in
          let class_info =
            match ty with
            | Miniml.Tglob (class_ref, type_args, _) -> Some (class_ref, type_args)
            | _ -> None
          in
          temps := (tt, instance_name, class_info, id) :: !temps;
          (instance_name, ty) )
      params
  in
  (params, List.rev !temps)

(** The value-parameter types, in declaration order, and the return type of
    a generated function declaration: what [CRANE_CHECK_IR] holds to its plan
    ({!declare_planned}). *)
let declared_signature : Cpp_ir.Lowered.Decl.t -> _ = function
  | Function {return_type; shape = Definition (params, _); _} ->
    Some {Callable_abi.params = List.map snd params; ret = return_type}
  | Function {return_type; shape = Declaration params; _} ->
    Some {Callable_abi.params = List.map snd params; ret = return_type}
  | _ -> None

(** The callable plan of [n], declared with the template head [temps] and
    the signature [declared]: both relaxed together
    ({!Plan_templates.relax_function_head}), the plan recording what the
    relaxations decided, which carry them through the declaration. *)
let plan_function_head ?deduced_callables ?passing ~minted n ty (temps : head_params)
    (declared : Callable_abi.signature) =
  let temps, signature, relaxations = relax_function_head temps declared in
  Callable_abi.of_head ?deduced_callables ?passing ~signature ~relaxations ~minted
    ~omitted:(Translation_support.type_arg_omission n)
    ~phantom_prefix:(Translation_types.leading_phantom_count n)
    ~relaxed:(fun i -> IntSet.mem i (Ml_type_util.relaxed_higher_kinded_tvars ty))
    ~callee:n ~scheme:(Mlutil.reference_scheme n) temps

(** What a function's body is generated under, settled before the body:
    its return type, its parameters and the environment that names them, the
    body as the signature renumbers it, under every parameter
    ({!Normalize.eta_expand}), and the head before the relaxations
    ({!plan_function_head}). *)
type body_scope = {
  bs_cod : Cpp_ir.Lowered.Type.t;
      (** The C++ return type: [unit] made [void], promoted variables
          resolved. *)
  bs_env : env;  (** Names every parameter, for de Bruijn lookup. *)
  bs_all_ids : (Id.t * ml_type) list;
      (** Every parameter, renamed, innermost first. *)
  bs_all_params : (ml_ident * ml_type) list;
      (** Every parameter as bound, innermost first: the eta-expansion ones,
          then the body's lambdas. *)
  bs_ids : (Id.t * Cpp_ir.Lowered.Type.t) list;
      (** The C++ value parameters, innermost first: dictionaries and erased
          binders left out, types wrapped by ownership. *)
  bs_missing : (ml_ident * ml_type) list;
      (** The parameters the body leaves to eta-expansion. *)
  bs_b : ml_ast;  (** The body, on the signature's type-variable numbering. *)
  bs_typeclass_temps_basic : head_params;
      (** The instance template parameters, constraints resolved. *)
  bs_regular_temps : head_params;
      (** The type parameters and the callable ones: what [Tvar] index
          resolution reads. *)
  bs_temps : head_params;
      (** The template head before the relaxations. *)
  bs_minted : (Id.t * Callable_abi.minted) list;
      (** What the builders of {!bs_temps} recorded of each parameter. *)
  bs_promoted_var_resolutions : (Id.t * Cpp_ir.Lowered.Type.t) list;
      (** Each promoted type variable, qualified through the instance
          parameter that provides it. *)
  bs_owned_flags : bool list;  (** Whether the body owns each of {!bs_all_ids}. *)
  bs_passing : Callable_abi.passing list;
      (** How each value parameter is passed, in declaration order. *)
  bs_self_call_undeducible : (Id.t -> bool) option;
      (** Under polymorphic recursion, the parameters a self-call has to
          write although the call is not at the declaration's own
          instantiation ({!self_call_reference}); [None] where it is. *)
  bs_gen_body_stmts : env -> (Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Stmt.t) -> ml_ast -> Cpp_ir.Lowered.Stmt.t list;
      (** Generates body statements with the signature's higher-kinded
          resolutions applied. *)
  bs_no_pure : bool;
      (** Whether [__attribute__((pure))] is withheld: a monadic result or a
          body that may throw. *)
  bs_deduced_callables : Param_pos.orig Param_pos.pos list;
      (** The declared positions of the callables deduced as an [F &&]. *)
}

(** Settle the {!body_scope} the function [n] is generated under, from its
    ML body [b].

    When the body has fewer lambda binders than the ML type's domain (i.e. it
    is under-applied), missing parameters are eta-expanded by synthesising
    [MLrel] arguments.  [Tdummy]-typed entries in the missing list are skipped:
    they represent erased type parameters (e.g. [A : Type] in
    [apply : forall A, A -> A]) that have no C++ runtime representation.
    Including them would produce a spurious [CPPabort "unreachable"] IIFE as an
    extra argument, causing [std::function] call sites to receive the wrong
    number of arguments.

    Settling the scope generates no body, so {!plan_function} runs it too, to
    plan the head without generating the function.

    @param n     the global reference for the function being defined
    @param b     the ML AST body
    @param cty   the C++ type of the function (decomposed internally into domain
                 and codomain)
    @param ty    the original ML type (used for domain decomposition and type
                 inference)
    @param temps template type parameters, and [minted] what their builder
                 recorded of each ({!Callable_abi.minted}) *)
let dfun_body_scope ~minted n b (cty : Cpp_ir.Lowered.Type.t) ty (temps : head_params) =
  let dom, cod =
    match cty with Function (d, c) -> (d, c) | t -> ([ (Void : Cpp_ir.Lowered.Type.t) ], t)
  in
  (* Suppress __attribute__((pure)) for functions whose ML return type is
     monadic — these perform side effects even though the C++ return type
     may look pure after type erasure. *)
  let no_pure = is_monadic_ml_type (ml_codomain ty) || ast_may_throw b in
  with_itree_mode_for ty @@ fun () ->
  (* Void-ify unit codomain: unit as return type maps to C++ void.
     Check the ML result type (unwrapping monad if present) to determine
     if the function returns unit. Then recursively replace the unit enum
     with Tvoid in the C++ codomain type.
     - Sequential mode: Unit → void directly (the monad wrapper is erased,
       so the C++ function literally returns void)
     - Reified mode: Tglob(itree, [E; Unit]) → Tglob(itree, [E; void])
       (printed as shared_ptr<ITree<void>> via monad template) *)
  let cod : Cpp_ir.Lowered.Type.t = if ml_type_is_void_call ty then Void else cod in
  (* Reversed: the lambda collection below peels the innermost arrow first. *)
  let mldom = List.rev (Ml_type_util.ml_domains ty) in
  let ids, b = collect_typed_lams ty b in
  (* The explicit lambdas bind the outermost domains; the eta-expansion
     parameters, the innermost ones -- for [R -> nat -> nat -> nat] with body
     [λr. <match>], [_x1 : nat; _x0 : nat], innermost first. *)
  let missing = unwritten_parameters ty ids b in
  (* A body's lambda parameter types agree with the signature's by now: the
     one Core rewrite that broke that, promoting a polymorphic let-fix to a
     top-level Dfix, unifies them where it promotes ([Modutil.decl_of_term]),
     before the program is frozen.  What a binder left open stays open
     ({!Miniml.Topen}), and is reconciled with the signature's type. *)
  let n_missing = List.length missing in
  let sig_types_for_ids =
    List.of_seq (Seq.drop n_missing (List.to_seq mldom))
  in
  let ids =
    if List.length ids = List.length sig_types_for_ids then
      List.map2
        (fun (id, body_ty) sig_ty -> (id, Core_query.reconcile_parameter_type body_ty sig_ty))
        ids sig_types_for_ids
    else ids
  in
  let tvar_subst_from_sig =
    if not (has_tvar ty)
       && List.length ids = List.length sig_types_for_ids then
      let rec chase = function
        | Miniml.Tmeta {contents = Some t} -> chase t
        | t -> t
      in
      let rec collect body_ty sig_ty acc =
        let body_ty = chase body_ty in
        let sig_ty = chase sig_ty in
        match (body_ty, sig_ty) with
        | (Miniml.Tvar (_, i)), _
          when not (has_tvar sig_ty) ->
          if List.mem_assoc i acc then acc else (i, sig_ty) :: acc
        | Miniml.Tglob (r1, ts1, _), Miniml.Tglob (r2, ts2, _)
          when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
          List.fold_left2 (fun acc a b -> collect a b acc) acc ts1 ts2
        | Miniml.Tarr (a1, b1), Miniml.Tarr (a2, b2) ->
          collect a1 a2 (collect b1 b2 acc)
        | _ -> acc
      in
      let direct = List.fold_left2
        (fun acc (_, body_ty) sig_ty -> collect body_ty sig_ty acc)
        [] ids sig_types_for_ids in
      if direct <> [] then direct
      else begin
        let all_body = List.map (fun (_, ty) -> ty) ids in
        let rec cross t1 t2 acc =
          let t1 = chase t1 in
          let t2 = chase t2 in
          match (t1, t2) with
          | (Miniml.Tvar (_, i)), _
            when not (has_tvar t2) ->
            if List.mem_assoc i acc then acc else (i, t2) :: acc
          | Miniml.Tglob (r1, ts1, _), Miniml.Tglob (r2, ts2, _)
            when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
            List.fold_left2 (fun acc a b -> cross a b acc) acc ts1 ts2
          | Miniml.Tarr (a1, b1), Miniml.Tarr (a2, b2) ->
            cross a1 a2 (cross b1 b2 acc)
          | _ -> acc
        in
        let pairs = List.concat_map (fun t1 ->
          List.concat_map (fun t2 ->
            if t1 == t2 then [] else cross t1 t2 []
          ) all_body
        ) all_body in
        List.fold_left (fun acc (i, t) ->
          if List.mem_assoc i acc then acc else (i, t) :: acc
        ) [] pairs
      end
    else
      []
  in
  let ids, b =
    match tvar_subst_from_sig with
    | [] -> (ids, b)
    | subst ->
      let apply_subst ty = subst_tvars_type subst ty in
      ( List.map (fun (id, ty) -> (id, apply_subst ty)) ids,
        map_types_in_ast apply_subst b )
  in
  (* Extraction numbers a type variable inside a body by the position of its
     binder among *all* the leading binders, while the recorded type numbers it
     among the type binders only.  A value binder that comes before a type
     binder -- a type-class instance, or [hk_map]'s [map_f] -- therefore shifts
     everything after it, and the body would name a template parameter that
     stands for something else.  Rebuild the correspondence from the binder
     kinds and put the body on the signature's numbering, which is the one the
     template parameters are named for.  The parameter types in [ids] have
     already been reconciled with the signature above, so only the body needs
     it.  The map is the identity whenever no value binder comes first, which
     is the common case. *)
  let b =
    let _, n_type_binders, renumbering =
      List.fold_left
        (fun (pos, rank, acc) dom ->
          match dom with
          | Miniml.Tdummy Miniml.Ktype ->
            let acc =
              if pos = rank then acc else (pos, Miniml.Tvar (Schematic, rank)) :: acc
            in
            (pos + 1, rank + 1, acc)
          | _ -> (pos + 1, rank, acc) )
        (1, 1, [])
        (Ml_type_util.ml_domains (try Table.find_type n with Not_found -> ty))
    in
    let n_type_binders = n_type_binders - 1 in
    (* Extraction does not always fall out of step: when the body happens to
       have been numbered against the type binders alone it is already right,
       and renumbering it again would move a variable off its own template
       parameter.  The one observable symptom of the mismatch is the body
       naming an index past the last type binder, which the signature
       numbering cannot produce, so take that as the trigger. *)
    let body_max =
      let m = ref 0 in
      ignore
        (map_types_in_ast
           (fun ty ->
             m := max !m (Mlutil.type_maxvar ty);
             ty )
           b);
      !m
    in
    (* An index past the last type binder is not proof on its own: a
       pattern's existential -- [VisF]'s answer type, numbered after the
       enclosing ones -- is one too.  A body numbered by position never names
       a value binder's position, though, so one that does is already on the
       signature's numbering. *)
    let value_positions =
      List.mapi (fun i dom -> (i + 1, dom))
        (Ml_type_util.ml_domains (try Table.find_type n with Not_found -> ty))
      |> List.filter_map (fun (i, dom) ->
             match dom with Miniml.Tdummy Miniml.Ktype -> None | _ -> Some i)
    in
    let names_a_value_position =
      let rec mentions t =
        match t with
        | Miniml.Tvar (_, i) -> List.mem i value_positions
        | Miniml.Tapp (i, l) -> List.mem i value_positions || List.exists mentions l
        | Miniml.Tglob (_, l, _) -> List.exists mentions l
        | Miniml.Tarr (a, c) -> mentions a || mentions c
        | Miniml.Tmeta {contents = Some t} -> mentions t
        | _ -> false
      in
      let found = ref false in
      ignore
        (map_types_in_ast
           (fun ty ->
             if mentions ty then found := true;
             ty )
           b);
      !found
    in
    let renumbering =
      if body_max > n_type_binders && not names_a_value_position then renumbering
      else []
    in
    match renumbering with
    | [] -> b
    | subst -> map_types_in_ast (subst_tvars_type subst) b
  in
  let all_params = missing @ ids in
  (* The callable parameters kept as [crane::fn] rather than promoted to
     template parameters below; they keep their [Tconst (Tfun(dom, cod))]
     type.  Asked of the body as it is generated, over every parameter it
     binds, so that one the definition leaves to eta-expansion is decided as
     it would be if written.  The indices are source order (param 0 = first
     Rocq parameter). *)
  let non_fwd_set =
    ungeneralised_callable_params ~self_ref:n
      ~suspended:(Table.is_coinductive_type (ml_return_type ty))
      (List.length all_params) b
  in
  (* Type class instance parameters become C++ template type parameters. We
     assign unique names (_tcI0, _tcI1, ...) to avoid collision with: - User
     variable names like 'i', 'j', etc. - Other generated names in the same
     scope The original parameter order is preserved for correct de Bruijn
     indexing. *)
  let all_params_for_env, typeclass_temps =
    promote_typeclass_params
      (List.map
         (fun (ml_id, ty) -> (cpp_id_of_id (id_of_mlid ml_id), ty))
         all_params )
  in
  (* Build a substitution map for PROMOTED TYPE VARIABLES: fields that were
     promoted from record values to type parameters during concept generation.

     When a function takes a typeclass parameter, references to that typeclass's
     promoted fields must be qualified as types (typename _tcI0::field), not
     accessed as values (_tcI0->field).

     Example:
       Coq function:
         Fixpoint mfold (M : Monoid) (l : list (m_carrier M)) : m_carrier M

       Extraction intermediate form:
         ML type has [Tglob(m_carrier, [])] ← marked as promoted type var
         Converts to [Tpromoted "m_carrier"] ← needs resolution

       This map provides the resolution:
         "m_carrier" ↦ Tqualified(Tvar(0, Some "_tcI0"), "m_carrier")
         Which prints as: typename _tcI0::m_carrier

     For nested typeclasses (e.g., PreStableCategory has a base_category : PreCategory),
     promoted vars are doubly qualified:
       "Obj" ↦ typename _tcI0::base_category::Obj

     The map is applied by [resolve_promoted_in_type] to substitute all
     [Tpromoted] markers with their qualified forms. *)
  let promoted_var_resolutions =
    List.concat_map
      (fun (_tt, tc_name, class_info, _) ->
        match class_info with
        | Some (class_ref, _) ->
          promoted_resolutions class_ref (Instance (tc_name, class_ref))
        | None -> [] )
      typeclass_temps
  in
  let hkt_tvar_resolutions = hkt_tvar_resolutions_of_type ty in
  (* Type annotations inside the body must name the same resolved types as the
     signature does. *)
  let gen_body_stmts env cw e =
    apply_hkt_resolutions_stmts hkt_tvar_resolutions (gen_stmts env cw e)
  in
  (* Substitute promoted type var markers [Tpromoted name] with their
     qualified resolutions throughout a C++ type tree. *)
  let resolve_promoted_in_type =
    Cpp_ir.Types.rewrite (fun (t : Cpp_ir.Lowered.Type.t) ->
      match t with
      | Variable (Index (i, _)) when List.mem_assoc i hkt_tvar_resolutions ->
        Some (List.assoc i hkt_tvar_resolutions)
      | Promoted_member name as ty ->
        Some
          ( match
              List.find_opt
                (fun (n, _) -> Id.equal n name)
                promoted_var_resolutions
            with
          | Some (_, resolved) -> resolved
          | None -> ty )
      | _ -> None )
  in
  (* Apply promoted var resolution to domain and codomain types *)
  let has_type_resolutions =
    promoted_var_resolutions <> [] || hkt_tvar_resolutions <> []
  in
  let dom =
    if has_type_resolutions then
      List.map resolve_promoted_in_type dom
    else dom
  in
  let cod =
    if has_type_resolutions then resolve_promoted_in_type cod else cod
  in
  (* Push params into environment for de Bruijn lookup during body generation.
     collect_typed_lams returns params in reverse order (innermost first), so
     MLrel 1 refers to the last param in the list.

     push_vars' may rename parameters to avoid collisions. For example, if Rocq
     has: fun (f : T) (f0 : F) (f : forest) => ... push_vars' renames the
     duplicate 'f' to 'f1', producing: [f; f0; f1]

     These renamed ids (all_ids) are used for both: 1. The environment (for
     correct de Bruijn lookup in the body) 2. The C++ function signature (so
     parameter names match body references).  A signature spelled with the
     original names would read [void foo(T f, F f0, forest f) { ... f1->v()
     ... }], where the body's [f1] matches no parameter. *)
  let all_ids, env = push_vars' all_params_for_env (empty_env ()) in
  reset_env_types ();
  push_parameters env all_ids;
  let n_params = List.length all_params in
  let owned_flags = infer_owned_flags ~owner:n b all_ids in
  (* Zip all_ids with ownership flags. all_ids and all_params have the same
     length (push_vars' preserves length), so owned_flags aligns 1:1. *)
  let all_ids_with_owned =
    List.map2 (fun (id, ty) owned -> (id, ty, owned)) all_ids owned_flags
  in
  (* The callables kept as [crane::fn], by binder: decided here, where every
     binder is still at its source position -- [all_ids] is innermost first,
     so the [p]th is source parameter [n_params - 1 - p] -- and read by name
     below, after the dictionaries and erased binders are filtered out. *)
  let kept_as_fn =
    List.fold_left
      (fun acc (p, (id, _)) ->
        if IntSet.mem (n_params - 1 - p) non_fwd_set then Id.Set.add id acc else acc )
      Id.Set.empty
      (List.mapi (fun p x -> (p, x)) all_ids)
  in
  (* For function signature, use renamed ids but exclude typeclass, void,
     and skipped-type params (e.g. ReSum instances from the ITree library
     that are not recognized by is_typeclass because ReSum's GlobRef is a
     ConstRef, not an IndRef registered in inductive_kinds). *)
  let ids_with_owned =
    List.filter
      (fun (_, ty, _) ->
        (not (Table.is_typeclass_type ty))
        && is_runtime_binder_type ty
        && not (is_skipped_ml_type ty) )
      all_ids_with_owned
  in
  (* Convert ML types to C++ types and wrap with const. Owned shared_ptr params:
     pass by value (shared_ptr<T>) Borrowed shared_ptr params: pass by const ref
     (const shared_ptr<T>&) *)
  let ids =
    List.map
      (fun (x, ty, owned) ->
        let cpp_ty = cpp_ir_of_ml_type env [] ty in
        let cpp_ty =
          if has_type_resolutions then resolve_promoted_in_type cpp_ty
          else cpp_ty
        in
        (* Reify monadic parameter types: itree E R → shared_ptr<ITree<R>> *)
        let cpp_ty = Translation_support.reify_monadic_param_type_ir ty cpp_ty in
        let wrapped = wrap_param_by_ownership_ir ~is_owned:owned ~core:ty cpp_ty in
        (x, wrapped) )
      ids_with_owned
  in
  (* Promote forwarded function-typed parameters to C++ template parameters.

     Function-typed parameters (those with C++ type [Tconst (Tfun(...))])
     are normally promoted to template parameters with [std::is_invocable_v]
     requires-clause constraints.  This replaces [const std::function<R(Args...)>]
     with a template type variable [F&&], giving the compiler the exact lambda
     type so it can inline the call body — no type-erasure overhead.

     For example, [tree_rect]'s two function parameters become:

       template <typename F0, typename F1>
         requires std::is_invocable_v<F0 &, unsigned int &>
               && std::is_invocable_v<F1 &, shared_ptr<tree> &, T1 &, ...>
       static T1 tree_rect(F0 &&f, F1 &&f0, ...);

     This works for [tree_rect] because its recursive calls pass [f] and
     [f0] unchanged — the template type stays the same at every recursion
     depth.

     Non-forwarded parameters are excluded from this promotion.  A parameter
     that receives a *different* expression at a recursive call site means the
     template type would be different at each recursion depth, causing
     infinite template instantiation.  These parameters keep their
     [const std::function<R(Args...)>] type, which is a concrete
     (non-template) type that stays the same regardless of wrapping.

     For example, [partition_cps p l k] has three parameters:
     - [p] is forwarded unchanged to the recursive call → template [F0 &&p]
     - [l] is not function-typed → stays as-is
     - [k] receives a different expression at the recursive call → [const std::function<...> k]

     Whether a callable is kept is read by binder ([kept_as_fn]), not by its
     position here, which the filtering above has shifted. *)
  (* Determine which tvars are "primary" — deducible from non-function domain
     params or the return type.  Function-typed params that reference tvars
     outside this set (e.g., erased HKT type variables) get TTtypename (no
     is_invocable_v constraint) instead of TTfun, to avoid referencing template
     type parameters that were filtered out as phantom
     ({!Plan_templates.phantom_aware_temps}, via {!with_function_head}). *)
  let primary = primary_tvar_indices_ir dom cod in
  let unwrap_fun_ty2 : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t option = function
    | Const (Function _ as f) | Reference (Lvalue, Const (Function _ as f)) -> Some f
    | Function _ as f -> Some f
    | _ -> None
  in
  let fun_tys =
    List.filter_map
      (fun (x, ty, i) ->
        match unwrap_fun_ty2 ty with
        | Some (Function (fdom, fcod) as f)
          when generalises_callable ~kept_as_fn:(Id.Set.mem x kept_as_fn) ~primary f ->
          let fun_idx = get_tvar_indices_ir f in
          let has_undeclared =
            List.exists (fun idx -> not (IntSet.mem idx primary)) fun_idx
          in
          if has_undeclared then
            Some (x, Cpp_ir.Template.Parameter_kind.Typename, fun_tparam_id i, i)
          else
            let fcod : Cpp_ir.Lowered.Type.t = if is_cpp_unit_type_ir fcod then Void else fcod in
            Some (x, Cpp_ir.Template.Parameter_kind.Callable_declared (fdom, fcod), fun_tparam_id i, i)
        | _ -> None )
      (List.mapi (fun i (x, ty) -> (x, ty, i)) (List.rev ids))
  in
  (* The declared positions of the callables deduced as an [F &&], which the
     plan records: a call site reads the decision there. *)
  let deduced_callables =
    let source = List.rev all_ids in
    let binder_tys = List.map snd source in
    let rec index_of x i = function
      | [] -> None
      | (y, _) :: rest -> if Id.equal x y then Some i else index_of x (i + 1) rest
    in
    List.filter_map
      (fun (x, _, _, _) -> Option.bind (index_of x 0 source) (Param_pos.of_source_index binder_tys))
      fun_tys
  in
  (* Replace the parameter type of promoted (forwarded) function params with the
     template type variable [F&&]. Non-forwarded params are left untouched — they
     keep [Tconst (Tfun(dom, cod))] which prints as [const
     crane::fn<R(Args...)>]. This loop iterates [ids] in de Bruijn order. *)
  let ids =
    List.mapi
      (fun i (x, ty) ->
        match unwrap_fun_ty2 ty with
        | Some (Function _ as f)
          when generalises_callable ~kept_as_fn:(Id.Set.mem x kept_as_fn) ~primary f ->
          ( x,
            (Reference (Forwarding, Variable (Named (fun_tparam_id (List.length ids - i - 1))))
              : Cpp_ir.Lowered.Type.t) )
        | _ -> (x, ty) )
      ids
  in
  (* A parameter whose type is a callable behind a type alias -- a one-method
     class demoted to [template <template <typename> class T> using C =
     std::function<...>] -- is one no argument can be deduced through: what
     arrives is a lambda, a lambda never has the alias's type, and deduction
     fails before the conversion that would have succeeded is considered.

     Taking it out of deduction is what lets the conversion happen.  The
     alternative, generalising it to an [F &&] the way a bare [Tfun] parameter
     is generalised above, would add a template parameter and so shift every
     explicit argument list that already names this function -- and there is
     nothing to gain by deducing a type the alias's own arguments, pinned by
     the other parameters, already determine. *)
  let ids =
    (* A type constructor standing in for a template parameter: the alias is
       applied to something of kind [Set -> Set], so the alias itself takes a
       [template <typename> class] parameter -- the shape C++ cannot deduce. *)
    let rec is_hk_arg (a : Cpp_ir.Lowered.Type.t) =
      match a with
      | Type_constructor _ -> true
      | Apply (Variable _, _) -> true
      | Const t | Reference (_, t) -> is_hk_arg t
      | _ -> false
    in
    (* The alias stands for a callable.  A struct behind an alias deduces
       perfectly well; it is only [std::function] that a lambda argument cannot
       match. *)
    let alias_rhs_is_fun kn =
      match Table.lookup_typedef_unchecked kn with
      | Some ml_ty -> (
        match cpp_ir_of_ml_type env [] ml_ty with
        | Function _ | Const (Function _) -> true
        | _ -> false )
      | None -> false
    in
    (* Whatever its arguments: a definitional class -- [Cat<T1, T2>], an
       alias for [std::function<...>] -- names this function's parameters, and
       a lambda argument cannot be matched against it.  A call site reads the
       same parameter as no source of deduction ([deducible_tvars_of_glob]),
       so the two agree on what has to be written. *)
    let rec alias_hides_fun (ty : Cpp_ir.Lowered.Type.t) =
      match ty with
      | Const t | Reference (_, t) -> alias_hides_fun t
      | Apply (Entity_application (GlobRef.ConstRef kn, [], _), args)
       |Entity_application (GlobRef.ConstRef kn, (_ :: _ as args), _) ->
        (List.exists is_hk_arg args || get_tvar_indices_ir ty <> [])
        && alias_rhs_is_fun kn
      | _ -> false
    in
    (* A callable parameter the recursion could not forward keeps its
       [std::function] spelling, and that is not a fallback: the type erasure
       is what makes the recursion close.  Rebuilding the callable at each step
       gives a new closure type at each step, so an [F &&] would instantiate a
       fresh specialisation forever.  But the spelling names this function's
       own template parameters, and a lambda argument never has that type --
       so the same deduction failure as the alias above, for the same reason,
       and the same repair.  Where the type names no parameter there is
       nothing to deduce and nothing to shield. *)
    let rec spelled_fun_is_deduced_against (ty : Cpp_ir.Lowered.Type.t) =
      match ty with
      | Const t | Reference (_, t) -> spelled_fun_is_deduced_against t
      | Function _ -> get_tvar_indices_ir ty <> []
      | _ -> false
    in
    (* The wrapper the ownership pass put on stays where it is; only the type
       it wraps is taken out of deduction. *)
    let rec at_core f (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
      match ty with
      | Const t -> Const (at_core f t)
      | Reference (k, t) -> Reference (k, at_core f t)
      | t -> f t
    in
    List.map
      (fun (x, ty) ->
        if alias_hides_fun ty || spelled_fun_is_deduced_against ty then
          ( x,
            at_core
              (fun t : Cpp_ir.Lowered.Type.t -> Non_deduced t)
              ty )
        else (x, ty) )
      ids
  in
  (* Add type class instance template parameters - instance types come first *)
  let typeclass_temps_basic =
    (* A constraint's arguments are types like any other and get the same
       resolution the signature does: [ToDvalueBase<_tcI0, T1, ptr, iptr>]
       spells the two promoted variables bare, and bare is the file-scope
       [std::any] rather than the [Params] instance standing beside it. *)
    List.map
      (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id, _, _) ->
        let tt : _ Cpp_ir.Template.Parameter_kind.t =
          match tt with
          | Concept (r, (_ :: _ as args)) when has_type_resolutions ->
            Concept (r, List.map resolve_promoted_in_type args)
          | tt -> tt
        in
        (tt, id) )
      typeclass_temps
  in
  (* A self-call writes what any call may write ({!self_call_reference}),
     at the declaration's own parameters -- except under polymorphic
     recursion.  A function recursing over a nested (non-uniform) inductive
     is at [nest (A * A)] in its self-call, not at [nest A], although Core
     records the call at its own variables (ML recursion is monomorphic).
     Repeating the enclosing template arguments would force the wrong
     instantiation, so let C++ deduce them from the argument instead -- the
     recursive argument always mentions the inductive, so deduction
     succeeds. *)
  let recurses_on_non_uniform_ind =
    let rec mentions : Cpp_ir.Lowered.Type.t -> bool = function
      | Entity_application (r, args, _) | In_namespace (r, Entity_application (_, args, _)) ->
        Table.is_non_uniform_inductive r || List.exists mentions args
      | Const t | In_namespace (_, t) | Reference (_, t) | Shared_pointer t -> mentions t
      | Function (d, c) -> List.exists mentions d || mentions c
      | _ -> false
    in
    List.exists (fun (_, ty) -> mentions ty) ids
  in
  (* ... unless the type parameters are erased out of the signature entirely
     (the inductive is rendered with [std::any] fields and the function takes
     no function-typed argument to name them).  Then no argument mentions
     them and deduction has nothing to work from -- but nothing in the body
     reads them either, so the self-call passes the enclosing parameters
     straight through.  That keeps the recursion to a single instantiation,
     and, unlike defaulting them, still rejects a caller that supplies
     nothing. *)
  let tvars_are_phantom = recurses_on_non_uniform_ind && fun_tys = [] in
  (* ... and unless one of them is spelled by no parameter while the result
     or a callable's constraint names it: the motive of a type-indexed
     family's recursor.  The family's C++ type takes no index, so nothing
     deduces it, and the recursion is at the one instantiation the result
     names.  The self-call writes it and the parameters before it, leaving
     those after it to deduction. *)
  let self_call_undeducible =
    if recurses_on_non_uniform_ind && not tvars_are_phantom then
      let spelled = List.concat_map (fun (_, ty) -> get_rendered_tvar_indices_ir ty) ids in
      let constrained =
        get_tvar_indices_ir cod
        @ List.concat_map
            (function
              | _, Cpp_ir.Template.Parameter_kind.Callable_declared (dom, cod), _, _ ->
                get_tvar_indices_ir (Function (dom, cod))
              | _ -> [])
            fun_tys
      in
      Some
        (fun id ->
          match List.find_opt (fun (_, id') -> Id.equal id id') temps with
          | Some (Typename_default _, _) | None -> false
          | Some _ -> (
            match List.assoc_opt id minted with
            | Some (Callable_abi.Scheme_param i) -> List.mem i constrained && not (List.mem i spelled)
            | _ -> false ) )
    else None
  in
  (* Combine all template params for function signature. Save the non-typeclass
     type params for Tvar index resolution below. *)
  let regular_temps = temps @ List.map (fun (_, t, n, _) -> (t, n)) fun_tys in
  (* Variables standing for a higher-kinded class parameter are rendered as
     associated types of the instance, so they must not also be declared as
     template parameters: nothing would deduce them.  They stay in
     [regular_temps] below, which only feeds Tvar index resolution. *)
  let is_hkt_temp (_, id) =
    List.exists (fun (i, _) -> Common.tvar_id i = id) hkt_tvar_resolutions
  in
  let temps =
    typeclass_temps_basic
    @ List.filter_map
        (fun t ->
          if is_hkt_temp t then None else Some t )
        regular_temps
  in
  {
    bs_cod = cod;
    bs_env = env;
    bs_all_ids = all_ids;
    bs_all_params = all_params;
    bs_ids = ids;
    bs_missing = missing;
    bs_b = b;
    bs_typeclass_temps_basic = typeclass_temps_basic;
    bs_regular_temps = regular_temps;
    bs_temps = temps;
    bs_minted =
      minted
      @ List.mapi (fun k (_, id, _, _) -> (id, Callable_abi.Instance_param k)) typeclass_temps
      @ List.map (fun (_, _, id, i) -> (id, Callable_abi.Callable_param i)) fun_tys;
    bs_promoted_var_resolutions = promoted_var_resolutions;
    bs_owned_flags = owned_flags;
    bs_passing =
      List.rev (List.map2 (fun (_, ty) (_, _, owned) -> param_passing_ir ~owned ty) ids ids_with_owned);
    bs_self_call_undeducible = self_call_undeducible;
    bs_gen_body_stmts = gen_body_stmts;
    bs_no_pure = no_pure;
    bs_deduced_callables = deduced_callables;
  }

(** The head of the function [n] generated under [scope], planned as its
    callers see it: outside the type-variable scope its body is generated in. *)
let plan_scope_head n ty scope =
  with_type_vars [] (fun () ->
      plan_function_head ~deduced_callables:scope.bs_deduced_callables ~passing:scope.bs_passing
        ~minted:scope.bs_minted n ty scope.bs_temps
        {Callable_abi.params = List.rev_map snd scope.bs_ids; ret = scope.bs_cod})

(** What the relaxations of the function [n] generated under [scope]
    decided: its plan's, which was made before anything was generated.
    Under [CRANE_CHECK_IR] the head is decided again from [scope] and checked
    against the plan. *)
let planned_relaxations n ty scope =
  if Probe.checking () then Callable_abi.check (plan_scope_head n ty scope);
  Callable_abi.relaxations (Callable_abi.planned n)

(** The global [r] at the type arguments [tys], with what its custom
    extraction inlines, if anything. *)
let entity_reference r tys : Cpp_ir.Lowered.Expr.t =
  Entity (r, tys, Some {inline = Option.map Cpp_ir.Foreign.template_of_text (Table.inline_custom_text r); custom_yields = None})

(** The reference a self-call of [n] in its own body is written with: every
    template parameter its plan lets a call write, at itself -- the call is
    at the declaration's own instantiation, so each is in scope and exact.
    That is not the policy of a call from elsewhere ({!Translation_calls.call_type_args}),
    which writes nothing a value argument deduces, the instantiation it reads
    possibly being unspellable.  Under polymorphic recursion
    ([undeducible]) the call is at another instantiation than Core records,
    so it writes only the dictionaries and the parameters up to the last one
    nothing deduces, leaving the rest to deduction. *)
let self_call_reference n ~undeducible =
  let writable =
    List.filter_map
      (fun p ->
        match (p.Callable_abi.write, p.Callable_abi.origin) with
        | Callable_abi.Deduce_only, _ | _, Callable_abi.From_callable _ -> None
        | _ -> Some (p.Callable_abi.origin, Callable_abi.Template_param.name p.Callable_abi.id) )
      (Callable_abi.template_head (Callable_abi.planned n))
  in
  let written =
    match undeducible with
    | None -> writable
    | Some undeducible ->
      let dicts, rest =
        List.partition
          (function Callable_abi.From_instance _, _ -> true | _ -> false)
          writable
      in
      let _, k =
        List.fold_left
          (fun (i, k) (_, id) -> (i + 1, if undeducible id then i + 1 else k))
          (0, 0) rest
      in
      dicts @ CList.firstn k rest
  in
  entity_reference n (List.map (fun (_, id) -> Cpp_ir.Build.named_variable id) written)

(** The declaration of the function [n] whose definition [decl] is, as its
    body was generated: the head is a projection of [n]'s plan -- the
    template head it declares ({!Callable_abi.declared_head}), and the
    value-parameter types and return type of its signature
    ({!Callable_abi.signature}) -- so the head a caller planned against is
    the one declared; [decl] gives only the parameter names and the body.
    Under [CRANE_CHECK_IR] the generated signature is held to the plan's.  A
    top-level sequential [main] keeps its own signature: it is declared to
    return [int] for the entry point, which no call of it reads. *)
let declare_planned n decl =
  let abi = Callable_abi.planned n in
  let is_entry_point =
    match (n, (decl : Cpp_ir.Lowered.Decl.t)) with
    | GlobRef.ConstRef c, Function {return_type = External ("int", []); _} ->
      String.equal (Label.to_string (Constant.label c)) "main"
    | _ -> false
  in
  let decl =
    if is_entry_point then decl
    else
      let planned = Callable_abi.signature abi in
      if Probe.checking () && not (Option.equal ( = ) planned (declared_signature decl)) then
        Probe.violation "callable ABI"
          Pp.(
            str "the declaration of " ++ GlobRef.print n
            ++ str " has another signature than its plan" );
      match (planned, decl) with
      | Some {Callable_abi.params; ret}, Function ({shape = Definition (ps, body); _} as f)
        when List.compare_lengths params ps = 0 ->
        Function {f with return_type = ret; shape = Definition (List.map2 (fun (id, _) t -> (id, t)) ps params, body)}
      | _ ->
        CErrors.anomaly
          Pp.(str "the definition of " ++ GlobRef.print n ++ str " does not have its plan's parameters.")
  in
  match Callable_abi.declared_head abi with
  | [] -> decl
  | head -> Template (head, None, decl)

(** Generate the C++ definition of the function [n] from its ML body [b]:
    its {!body_scope}, the head its plan declares, the body with every
    self-call written as {!self_call_reference} says, the sigma-type
    precondition assertions, and the entry-point rewrite of a monadic
    [main].  Returns the declaration, wrapped in its template head when it
    has one, and the environment its parameters were named in.

    @param n     the global reference for the function being defined
    @param b     the ML AST body
    @param cty   the C++ type of the function (decomposed internally into domain
                 and codomain)
    @param ty    the original ML type
    @param temps template type parameters, and [minted] what their builder
                 recorded of each ({!Callable_abi.minted}) *)
let gen_dfun ~minted n b cty ty temps =
  let scope = dfun_body_scope ~minted n b cty ty temps in
  let relaxations = planned_relaxations n ty scope in
  let rec_call = self_call_reference n ~undeducible:scope.bs_self_call_undeducible in
  let inner, env =
    with_itree_mode_for ty @@ fun () ->
  let {
    bs_env = env;
    bs_all_ids = all_ids;
    bs_all_params = all_params;
    bs_missing = missing;
    bs_b = b;
    bs_typeclass_temps_basic = typeclass_temps_basic;
    bs_regular_temps = regular_temps;
    bs_owned_flags = owned_flags;
    bs_gen_body_stmts = gen_body_stmts;
    bs_no_pure = no_pure;
    _
  } =
    scope
  in
  let cod = scope.bs_cod in
  (* Set current type variables for pattern matching lambda generation.
     These are the template parameters that can be used in type annotations.
     Exclude typeclass instance params — they are not ML type variables
     and should not participate in Tvar index resolution.

     The scope is read by ML variable -- entry [i - 1] names [Tvar i] -- and
     the head is not: it leaves out a variable the C++ type never spells
     ([after_family]'s [A], mentioned only by an erased family), and a
     parameter declared for scheme variable [i] ({!Callable_abi}) is then
     not the head's [i]th.  Where the head's builder recorded the variables
     its parameters are for ({!Callable_abi.minted}), the scope is laid out
     by those numbers; a variable the head omits
     keeps its own name, which nothing declares, rather than taking a
     neighbour's. *)
  let type_var_ids =
    let declared =
      List.filter_map
        (fun ((tt : _ Cpp_ir.Template.Parameter_kind.t), id) ->
          match tt with
          | Typename | Typename_default _ | Template _ -> Some id
          | _ -> None )
        regular_temps
    in
    let scheme_number id =
      match List.assoc_opt id scope.bs_minted with
      | Some (Callable_abi.Scheme_param i) -> Some i
      | _ -> None
    in
    match List.filter_map scheme_number declared with
    | [] -> declared
    | numbers -> List.init (List.fold_left max 0 numbers) (fun k -> tvar_id (k + 1))
  in
  set_current_type_vars type_var_ids;
  (* The head itself, at the kinds it declares: see
     {!Translation_state.current_template_head}. *)
  let saved_template_head = get_current_template_head () in
  set_current_template_head (typeclass_temps_basic @ regular_temps);
  (* Activate promoted var resolution for body generation — types like
     [Tpromoted "Obj"] in type annotations will be resolved to
     qualified access through the typeclass instance chain. *)
  let saved_promoted_var_map = (!tctx).promoted_var_map in
  (* Extend, never replace.  This declaration's own instance parameters answer
     first -- a variable they declare is the one the body is written in -- but
     what {!with_body_resolutions} read from the body and from the declarations
     it names is the only answer a function with no instance parameter of its
     own has.  [check : unit -> nat] whose body applies [@runS (@ParamsV
     natIPtr)] has none, and replacing the map dropped the answer on the way
     in, so the body spelled the file-scope erased alias in a scope that knew
     the instance perfectly well. *)
  tctx :=
    { !tctx with
      promoted_var_map = scope.bs_promoted_var_resolutions @ saved_promoted_var_map };
  (* Name the declaration being generated: inner fixpoints lifted out of it
     take their identity from it. *)
  let saved_decl_ref = !Table.current_decl_ref in
  Table.current_decl_ref := Some n;
  (* A coinductive value is suspended at its constructors (see
     [suspend_ctor]); the body around them runs where it is called.  Only a
     body that calls itself outside every constructor -- guarded, for Rocq,
     only up to unfolding -- is suspended whole. *)
  let ml_ret = ml_return_type ty in
  let is_cofix_return = Translation_support.suspends_whole n ml_ret b in
  let cofix_wrap (x : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Stmt.t =
    if is_cofix_return then
      suspend_whole ~cpp_of:(cpp_ir_of_ml_type env type_var_ids) ~cod ml_ret x
    else if cod = Void then
      (* void function: execute expression for side effects, then return.
         Some tail expressions (like writeTVar) have side effects that must
         not be discarded. Skip pure expressions (variables, enum values,
         inline-custom literals like std::monostate{}) to avoid dead-code
         warnings. *)
      ( match x with
      | Enum_value _ | Local _ | Literal (Int _) | Literal (Float _) | Foreign_text _ ->
        Return None
      | Entity (_, _, Some ci) when ci.inline <> None -> Return None
      | _ -> Block [Expression x; Return None] )
    else
      Return (Some x)
  in
  (* Generate sigma type precondition assertions *)
  let sigma_asserts =
    let assertions = Table.get_sigma_assertions n in
    if assertions = [] then
      []
    else
      let all_id_arr = Array.of_list (List.rev all_ids) in
      (* outermost param first; [all_params] runs in the same order and
         carries the ML types, which say whether a parameter is a [sig]. *)
      let all_ml_arr = Array.of_list (List.rev all_params) in
      (* A template's placeholders are numbered outwards from the parameter
         the assertion was registered for: [%0] is that parameter's witness,
         [%1] the binder before it, and so on.  Substituting the highest index
         first keeps [%10] from being read as [%1] followed by a digit. *)
      let render param_idx witness_of template =
        let substs =
          List.init (param_idx + 1) (fun k ->
            let name = Id.to_string (fst all_id_arr.(param_idx - k)) in
            ( Printf.sprintf "%%%d" k,
              if k = 0 then witness_of name (snd all_ml_arr.(param_idx - k))
              else Some name ) )
        in
        let substs =
          List.filter_map
            (fun (ph, r) -> Option.map (fun r -> (ph, r)) r)
            substs
        in
        Common.render_template (List.rev substs) template
      in
      (* The assertion holds of the parameter's witness, so it can only be
         made when the witness has an expression; failing that -- and failing
         a placeholder naming a binder outside this parameter's reach -- the
         precondition is reported rather than checked, still spelling the
         parameters it speaks of. *)
      let subst_placeholders param_idx template =
        let stated = render param_idx sig_witness_expr template in
        if String.contains stated '%' then
          Error (render param_idx (fun name _ -> Some name) template)
        else Ok stated
      in
      List.filter_map
        (fun (param_idx, assertion) ->
          if param_idx >= Array.length all_id_arr then
            None
          else
            match
              assertion
            with
            | Table.AssertExpr template ->
              ( match subst_placeholders param_idx template with
              | Ok expr_str -> Some (Cpp_ir.Stmt.Assert (Checked expr_str) : Cpp_ir.Lowered.Stmt.t)
              | Error comment -> Some (Assert (Stated comment)) )
            | Table.AssertComment comment -> Some (Assert (Stated comment)) )
        assertions
  in
  begin_body ~owner:n ~function_:true ();
  set_current_parameters (List.map snd (parameter_binders env all_ids));
  let resumes = Control_to_cpp_ir.function_resumes n ~depth:(List.length all_ids) in
  (* The parameters the body owns, at de Bruijn indices 1..n_params: those
     the head declares by value. *)
  let owned_params =
    Translation_support.owned_parameters (List.length owned_flags)
      ~owned:(fun i ->
        match List.assoc_opt (fst (List.nth all_ids i)) scope.bs_ids with
        | Some ty -> not (Translation_support.declared_by_reference_ir ty)
        | None -> List.nth owned_flags i )
      ~declared:(fun i -> List.assoc_opt (fst (List.nth all_ids i)) scope.bs_ids)
      ~ty:(fun i -> snd (List.nth all_params i))
  in
  (* Expose the C++ return type to inner call sites so they can recover erased
     template type args (see try_recover_erased_return_type). *)
  let saved_return_type = (!tctx).current_cpp_return_type in
  tctx := { !tctx with current_cpp_return_type = Some scope.bs_cod };
  (* For non-inlined custom constants (axioms mapped via Crane Extract
     Constant), generate a forwarding body that delegates to the custom
     implementation instead of the default CPPabort throw. *)
  let custom_forwarding_body =
    match b with
    | MLaxiom _ when is_custom n && not (to_inline n) ->
      let custom_name = find_custom n in
      let param_vars = List.map (fun (id, _) : Cpp_ir.Lowered.Expr.t -> Local id) scope.bs_ids in
      Some [(Return (Some (Cpp_ir.Build.call (Foreign_text custom_name) param_vars)) : Cpp_ir.Lowered.Stmt.t)]
    | _ -> None
  in
  (* A self-call written at another instance keeps the template arguments
     translation gave it; every other reference to [n] is [rec_call]. *)
  let spare = other_instance_self_calls n b in
  (* method_self_ns is extended by the caller ([gen_decl__inner], or
     {!with_function_head} for the others, through [with_method_ns_for_locals])
     before computing cty, so it's already active here. *)
  (* The guard of [Crane Guard Compare], in front of the body. *)
  let guarded body = Translation_support.guard_compare_ir n scope.bs_ids body in
  let definition body : Cpp_ir.Lowered.Decl.t =
    Function
      { path = {outer = (n, []); inner = []};
        return_type = scope.bs_cod;
        no_pure;
        constexpr = Undecided;
        shape = Definition (List.rev scope.bs_ids, finish_fn_body_ir scope.bs_cod (guarded (sigma_asserts @ body)));
        binders = parameter_binders env scope.bs_ids;
        loop = None }
  in
  let inner =
    if missing == [] then (
      let b =
        match custom_forwarding_body with
        | Some stmts -> stmts
        | None ->
          let b =
            List.map (glob_subst_stmt_ir ~spare n rec_call)
              (with_region ~owned:owned_params ?resumes b (fun () -> gen_body_stmts env cofix_wrap b))
          in
          return_captures_by_value_ir b
      in
      clear_current_type_vars ();
      set_current_parameters [];
      definition b )
    else
      (* An axiom or exception body, which always throws, is the one that
         binds fewer parameters than the head declares
         ({!Ml_type_util.unwritten_parameters}). *)
      let b =
        match custom_forwarding_body with
        | Some stmts -> stmts
        | None ->
        match b with
        | MLaxiom _ | MLexn _ ->
          List.map (glob_subst_stmt_ir ~spare n rec_call) (gen_stmts env cofix_wrap b)
        | _ ->
          List.map
            (glob_subst_stmt_ir ~spare n rec_call)
            (with_region ~owned:owned_params ?resumes b (fun () -> gen_body_stmts env cofix_wrap b))
      in
      let b = return_captures_by_value_ir b in
      clear_current_type_vars ();
      set_current_parameters [];
      definition b
  in
  tctx := { !tctx with current_cpp_return_type = saved_return_type };
  Table.current_decl_ref := saved_decl_ref;
  tctx := { !tctx with promoted_var_map = saved_promoted_var_map };
  set_current_template_head saved_template_head;
  (* {b Entry point detection for monadic [main].}

     When a Rocq definition named [main] has a monadic return type, it is
     treated as the program entry point.  The generated C++ must provide a
     standard [int main()] — the handling depends on two factors:

     {b 1. Inside a struct} ([struct_name = Some _]):
       The function keeps its original name.  [Struct::main()] does not
       collide with the free [int main()] because C++ member functions
       occupy a separate scope.  A wrapper [int main() \{ Struct::main(); \}]
       is generated by [Extract_env.print_structure_to_file] from the
       {!Table.set_main_function} registration.

     {b 2. Top-level, sequential mode} ([struct_name = None, needs_run = false]):
       The monad is erased (sequential ITree mode), so the function body is
       plain imperative C++ returning [void].  Instead of emitting a separate
       [_main] + wrapper, we convert the definition directly into
       [int main()] by changing the return type to [int] and replacing every
       [Sreturn None] (i.e. [return;]) with [Sreturn (Some (CPPint 0))]
       (i.e. [return 0;]).  No wrapper is needed.

     {b 3. Top-level, reified mode} ([struct_name = None, needs_run = true]):
       The function returns [shared_ptr<ITree<R>>] and must be called with
       [->run()] to execute the interaction tree.  We rename the function to
       [_main] (to avoid colliding with the free [int main()]) and register
       it for wrapper generation: [int main() \{ _main()->run(); return 0; \}]. *)
  let inner = match n with
    | GlobRef.ConstRef c ->
      let label_str = Label.to_string (Constant.label c) in
      if label_str = "main" && is_monadic_ml_type (ml_codomain ty) then begin
        let struct_name =
          let mp = Constant.modpath c in
          match mp with
          | ModPath.MPdot (_, l) -> Some (Id.of_string (Label.to_string l))
          | _ -> None
        in
        let needs_run = match resolve_tmeta (ml_codomain ty) with
          | Tglob (r, _, _) -> is_monad_reified r
          | _ -> false
        in
        match struct_name, needs_run with
        | Some _, _ ->
          (* Case 1: inside a struct — keep name, register for wrapper *)
          Table.set_main_function (Id.of_string "main") (ml_codomain ty) struct_name needs_run;
          inner
        | None, false ->
          (* Case 2: top-level sequential — emit [int main()] directly.
             Replace [Tvoid] return type with [int] and every [Sreturn None]
             with [Sreturn (Some (CPPint 0))]. *)
          let int_ty : Cpp_ir.Lowered.Type.t = External ("int", []) in
          let rec void_return_to_zero : Cpp_ir.Lowered.Stmt.t -> Cpp_ir.Lowered.Stmt.t = function
            | Return None -> Return (Some (Literal (Int 0)))
            | If i -> If {i with then_ = List.map void_return_to_zero i.then_; else_ = List.map void_return_to_zero i.else_}
            | Block ss -> Block (List.map void_return_to_zero ss)
            | Match (scrut, branches, default) ->
              Match
                ( scrut,
                  List.map
                    (fun (br : _ Cpp_ir.Stmt.Match.branch) -> {br with body = List.map void_return_to_zero br.body})
                    branches,
                  Option.map (List.map void_return_to_zero) default )
            | s -> s
          in
          ( match inner with
          | Function ({shape = Definition (params, body); _} as f) ->
            Function {f with return_type = int_ty; shape = Definition (params, List.map void_return_to_zero body)}
          | d -> d )
        | None, true ->
          (* Case 3: top-level reified — rename to [_main], register for
             wrapper that calls [_main()->run()] *)
          let new_label = Label.of_id (Id.of_string "_main") in
          let new_n = GlobRef.ConstRef (Constant.make2 (Constant.modpath c) new_label) in
          Table.set_main_function (Id.of_string "_main") (ml_codomain ty) None needs_run;
          ( match inner with
          | Function f -> Function {f with path = {outer = (new_n, []); inner = []}}
          | d -> d )
      end else
        inner
    | _ -> inner
  in
    (inner, env)
  in
  (declare_planned n (Head_relaxation.apply_all relaxations inner), env)

(** Whether a recovered type names an associated type of the enclosing class,
    and so is worth writing back into the binder it came from.  Anything else
    in a body already has a pass that reads it from somewhere better than the
    declaration -- an alias, for one, is a type in its own right and the body
    wants the type it stands for. *)
let rec names_promoted_type_var = function
  | Miniml.Tglob (r, args, _) ->
    Table.is_promoted_type_var r || List.exists names_promoted_type_var args
  | Miniml.Tarr (a, b) -> names_promoted_type_var a || names_promoted_type_var b
  | Miniml.Tmeta {contents = Some t} -> names_promoted_type_var t
  | _ -> false

(** Whether a recovered type says something that means the same at the hole as
    it did in the declaration.

    The gate above asks whether the {e offer} names a promoted type var, which
    is too narrow: the population it misses is the one where the declaration
    knows a perfectly ordinary type.  [memS_mon::bind] declares its
    continuation [std::function<MemS<..,_A1>(_A0)>] and the call is
    [bind<unit, unit>], so the answer [unit] is spelled one line above the
    binder -- and [unit] names no promoted type var.

    A type with no variable in it is one this pass can only get right.  It
    mentions nothing whose meaning depends on where it is read, so it means
    the same at the binder as it did in the declaration.  A variable does not:
    [itreeF]'s [Vis] quantifies over the event's result as well as the tree's,
    and a call that instantiates that existential at the caller's own third
    variable offers a name which, read at the lambda, denotes the deduced type
    of a function parameter.  That offer is faithful to the term and still
    unusable, so variables stay out.

    [Tdummy] is out for the same reason read the other way round: an erased
    position says nothing anywhere, so an offer carrying one cannot beat the
    guess at the same hole -- it only respells [List<T3>] as [List<std::any>].
    Closed is the wrong word for it; the predicate wants types that are both
    closed and informative, and [Tdummy] is the canonical uninformative one. *)
let rec is_closed_type = function
  | Miniml.Tglob (_, args, _) -> List.for_all is_closed_type args
  | Miniml.Tarr (a, b) -> is_closed_type a && is_closed_type b
  | Miniml.Tmeta {contents = Some t} -> is_closed_type t
  | Miniml.Tstring -> true
  | Miniml.Tdummy _ | Miniml.Tvar _ | Miniml.Tapp _ | Miniml.Thole _
  | Miniml.Tmeta {contents = None} | Miniml.Topen _ | Miniml.Tunknown | Miniml.Taxiom ->
    false

(** Whether the second recovery pass may write a recovered type into its
    binder: it names a promoted type var or is closed and informative. *)
let writable_offer ty = names_promoted_type_var ty || is_closed_type ty

(** Fill a body's empty type annotations from the declaration, in two passes.

    The first pass is the narrow one and the second widens it: a hole the
    declaration names perfectly well -- but which happens not to mention a
    promoted type var -- would otherwise be declined by the one pass that
    knows the answer.

    A hole neither pass can name is left a hole.  Filling it with the
    enclosing class's first-declared associated type would be right only when
    the class declares exactly one and the hole is the carrier; where it is
    not, the guess is what the body is printed from, and it pre-empts the
    passes in {!Translation} that can still read the answer off the term. *)
let recover_erased_body_types ty b =
  let b = Mlutil.recover_erased_types ~only:names_promoted_type_var ty b in
  Mlutil.recover_erased_types ~only:writable_offer ~refine_only:true ty b

(** A constant's initialiser: its body, or -- for an erased proof, a lemma of
    a module whose other members are extracted -- the empty box an erased
    constructor argument is.  The [MLdummy] case of {!Translation.gen_expr}
    is for dead code, an abort; a constant is evaluated, at static
    initialisation. *)
let gen_constant_value ?expected_ty b =
  match b with
  | MLdummy _ -> Cpp_erasure.empty_box_ir
  | _ -> gen_expr ?expected_ty (empty_env ()) b

(** The parameters a head declares for the type variables [cty] spells,
    and for the ML variables [extra] it does not, by the variable each
    stands for: the name {!Plan_templates.phantom_aware_temps} gives it. *)
let scheme_params ?(extra = IntSet.empty) (cty : Cpp_ir.Lowered.Type.t) =
  let spelled =
    List.filter (fun (i, _) -> i > 0) (Ml_type_util.get_tvars_indexed_ir cty)
  in
  List.map (fun (i, id) -> (id, Callable_abi.Scheme_param i)) spelled
  @ List.filter_map
      (fun i ->
        if List.mem_assoc i spelled then None
        else Some (Common.tvar_id i, Callable_abi.Scheme_param i) )
      (IntSet.elements extra)

(** A function reaching a generator for what is not one: a function's head
    is a projection of its plan ({!declare_planned}), and {!plan_function}
    planned it only where {!gen_decl_for_pp} generates it. *)
let function_without_plan n =
  CErrors.anomaly
    Pp.(str "the function " ++ GlobRef.print n ++ str " is generated as a constant, with no plan.")

(** The function of no parameters [n] returning [body], the value of C++
    type [ret] translation generated, which a call computes. *)
let thunk n ret body : Cpp_ir.Lowered.Decl.t =
  Function
    { path = {outer = (n, []); inner = []};
      return_type = ret;
      no_pure = false;
      constexpr = Undecided;
      shape = Definition ([], [Return (Some body)]);
      binders = [];
      loop = None }

(** The constant [n] of C++ type [ty], initialised with [init], the value
    translation generated. *)
let variable n ty init : Cpp_ir.Lowered.Decl.t =
  Variable {ref_ = n; type_ = ty; init; constexpr = Undecided}

(** Generate the C++ declaration of [n], which is not a function, from its
    ML definition: a constant whose body only throws (as a zero-argument
    function), or a constant initialised with its value.  Returns the
    declaration, its environment and the C++ type's variables. *)
let gen_decl__inner n b ty =
  with_body_resolutions n b @@ fun () ->
  with_itree_mode_for ty @@ fun () ->
  with_method_ns_for_locals @@ fun () ->
  let cty_ir = cpp_ir_of_ml_type (empty_env ()) [] ty in
  let tvars = get_tvars_ir cty_ir in
  let temps = Cpp_ir.Build.typenames tvars in
  let templated inner = match temps with [] -> inner | l -> Cpp_ir.Decl.Template (l, None, inner) in
  match cty_ir with
    | Function _ -> function_without_plan n
    | _ ->
    match b with
    | _ when thunk_reason n = Some Throws ->
      (* A body that only throws becomes a zero-arg function, so the throw
         happens when the value is asked for rather than during static
         initialisation (which terminates the program before main). *)
      let body_expr = with_region b (fun () -> gen_expr (empty_env ()) b) in
      (templated (thunk n cty_ir body_expr), empty_env (), tvars)
    | _ ->
      begin_body ~owner:n ();
      let body_expr =
        with_cpp_return_type_ir (Some cty_ir) (fun () -> with_region b (fun () -> gen_constant_value b))
      in
      (* When a unit-typed constant's body calls a void-ified function,
         the call produces no value.  Wrap in an IIFE that executes the
         body for side effects and returns Unit::e_TT. *)
      let body_expr =
        if is_cpp_unit_type_ir cty_ir then
          match body_expr with
          | Enum_value _ -> body_expr  (* already a literal *)
          | Entity (_, _, Some ci) when ci.inline <> None ->
            body_expr  (* inline custom literal (e.g. std::monostate{}) *)
          | _ -> Cpp_ir.Build.iife None [Expression body_expr; Return (Some (mk_tt_expr ()))]
        else body_expr
      in
      let body_expr =
        match Translation_types.slot_repr_of_cpp_type_ir cty_ir with
        | Boxed kind -> box_for_any_slot kind b body_expr
        | Native -> body_expr
      in
      (templated (deapply_plain_tvars temps (variable n cty_ir body_expr)), empty_env (), tvars)

(** {!gen_decl__inner} with [n] as the declaration being generated. *)
let gen_decl n b ty =
  Table.with_decl_ref n (fun () -> gen_decl__inner n b ty)

(** What a top-level function is generated under: its body with erased types
    recovered and type variables resolved against its ML type, its C++ type,
    its template head, and the template parameters callers must see. *)
type function_head = {
  fh_body : ml_ast;
  fh_cty : Cpp_ir.Lowered.Type.t;
  fh_temps : head_params;
  fh_minted : (Id.t * Callable_abi.minted) list;
      (** The variable each of {!fh_temps} is declared for. *)
  fh_tvars : Id.t list;
      (** Typeclass-typed parameters first -- they become template parameters
          inside {!gen_dfun} without appearing in the C++ type, and a caller
          must see them to use the full template definition -- then the C++
          type's variables and the index variables it does not mention. *)
}

(** [with_function_head n b ty k] establishes the scope a top-level function
    [n] is generated in and hands [k] its {!function_head}. *)
let with_function_head n b ty k =
  with_body_resolutions n b @@ fun () ->
  let ty = type_simpl ty in
  let b = recover_erased_body_types ty b in
  let b = resolve_body_tvars b ty in
  with_method_ns_for_locals @@ fun () ->
  let cty = cpp_ir_of_ml_type (empty_env ()) [] ty in
  let tvars = List.map snd (Ml_type_util.get_tvars_indexed_ir cty) in
  let index_tvar_set = collect_ml_type_index_tvars ty in
  let extra_index_tvars =
    IntSet.fold (fun i acc ->
      let id = Common.tvar_id i in
      if List.exists (Id.equal id) tvars then acc
      else id :: acc
    ) index_tvar_set []
    |> List.rev
  in
  let tvars = tvars @ extra_index_tvars in
  let temps =
    phantom_aware_temps ~force_required:index_tvar_set
      ~also_declared:(Ml_type_util.collect_ml_tvars ty) ~ml_ty:ty cty tvars
  in
  let tc_param_ids =
    match ty with
    | Tarr _ -> collect_typeclass_param_ids ty
    | _ -> []
  in
  let minted =
    scheme_params ~extra:(IntSet.union index_tvar_set (Ml_type_util.collect_ml_tvars ty)) cty
  in
  k ty
    { fh_body = b;
      fh_cty = cty;
      fh_temps = temps;
      fh_minted = minted;
      fh_tvars = tc_param_ids @ tvars }

(** [gen_function n ty h] generates the function [n] under [h]: its
    definition, the environment its names were allocated in, and the template
    parameters callers see -- [h]'s, then one per callable parameter. *)
let gen_function n ty h =
  let f, env = gen_dfun ~minted:h.fh_minted n h.fh_body h.fh_cty ty h.fh_temps in
  let callable_tparams =
    match h.fh_cty with
    | Function (dom, _) ->
      List.filter_map
        (fun ((ty : Cpp_ir.Lowered.Type.t), i) ->
          match ty with
          | Function _ when not (Ml_type_util.is_fully_erased_fun_ty_ir ty) ->
            Some (fun_tparam_id i)
          | _ -> None )
        (List.mapi (fun i ty -> (ty, i)) dom)
    | _ -> []
  in
  (f, env, h.fh_tvars @ callable_tparams)

(** [plan_function ~fixpoint n b ty] is the callable plan of the function
    [n] -- [b] its body, [ty] its type -- as generating it would plan it,
    without generating the body.  A member of a recursive group is always
    generated as a function; a constant only where its C++ type is one. *)
let plan_function ~fixpoint n b ty =
  Table.with_decl_ref n @@ fun () ->
  with_function_head n b ty @@ fun ty h ->
  let plan cty =
    let abi = plan_scope_head n ty (dfun_body_scope ~minted:h.fh_minted n h.fh_body cty ty h.fh_temps) in
    ( if Probe.checking () then
        match cpp_ir_of_ml_type (empty_env ()) [] ty with
        | live -> Translation_support.check_planned_arity_ir abi live
        | exception e when CErrors.noncritical e -> () );
    Some abi
  in
  match h.fh_cty with
  | Function _ as cty -> plan cty
  | cty when fixpoint -> plan cty
  | _ -> None

(** Generate C++ declaration with pretty-printing adjustments: a function, a
    constant whose body only throws (as a zero-argument function, so it
    throws when called and not at static initialisation), or [None] for any
    other constant. *)
let gen_decl_for_pp__inner n b ty =
  with_function_head n b ty @@ fun ty h ->
  match h.fh_cty with
  | Function _ ->
    let f, env, tvars = gen_function n ty h in
    (Some f, env, tvars)
  | cty when thunk_reason n = Some Throws ->
    let body_expr = gen_expr (empty_env ()) h.fh_body in
    let inner = thunk n cty body_expr in
    let ds = match h.fh_temps with [] -> inner | l -> Template (l, None, inner) in
    (Some ds, empty_env (), h.fh_tvars)
  | _ -> (None, empty_env (), h.fh_tvars)

(** {!gen_decl_for_pp__inner} with [n] as the declaration being generated. *)
let gen_decl_for_pp n b ty =
  Table.with_decl_ref n (fun () -> gen_decl_for_pp__inner n b ty)

(** Generate a full C++ function definition for a [Dfix] member.  Returns
    [(decl, env, tvars)]. *)
let gen_dfun_def__inner n b ty = with_function_head n b ty (gen_function n)

(** {!gen_dfun_def__inner} with [n] as the declaration being generated. *)
let gen_dfun_def n b ty =
  Table.with_decl_ref n (fun () -> gen_dfun_def__inner n b ty)

(** Generate the C++ specification of [n], which is not a function, for a
    header: a throwing constant's zero-argument declaration, or a constant's
    initialised definition. *)
let gen_spec__inner n b ty =
  with_body_resolutions n b @@ fun () ->
  with_itree_mode_for ty @@ fun () ->
  let ty = type_simpl ty in
  let ml_ty = ty in  (* preserve ML type before C++ conversion *)
  with_method_ns_for_locals @@ fun () ->
  let ty_ir = cpp_ir_of_ml_type (empty_env ()) [] ty in
  let temps = Cpp_ir.Build.typenames (get_tvars_ir ty_ir) in
  let templated inner = match temps with [] -> inner | l -> Cpp_ir.Decl.Template (l, None, inner) in
  let result =
    match ty_ir with
    | Function _ -> function_without_plan n
    | _ ->
    match b with
    | _ when thunk_reason n = Some Throws ->
      (* Throws when called, so: a zero-arg function declaration. *)
      let inner : Cpp_ir.Lowered.Decl.t =
        Function
          { path = {outer = (n, []); inner = []};
            return_type = ty_ir;
            no_pure = false;
            constexpr = Undecided;
            shape = Definition ([], []);
            binders = [];
            loop = None }
      in
      (templated inner, empty_env ())
    | _ ->
      (* Expose the constant's C++ type so that inner call sites can recover
         erased template type args (see try_recover_erased_return_type). Without
         this, calls like pick<natBoxed>() inside a constant body cannot deduce
         the missing type parameter. *)
      with_cpp_return_type_ir (Some ty_ir) @@ fun () ->
      (* Strip MLmagic wrapper and track whether a type coercion from std::any
         is needed.  MLmagic wraps expressions when the extraction detects a
         type mismatch (e.g. Obj = std::any vs nat = unsigned int).  The body
         is canonical ({!Core_normalize}), so no application in it has a
         coercion at its head. *)
      let has_magic, inner_body =
        match b with
        | MLmagic (_, inner, _) -> (true, inner)
        | _ -> (false, b)
      in
      (* A constant typed by a name -- an instance of a single-method class is
         typed by the class -- may be initialised with a partially applied
         body: [Instance Convert_holder : Convert hbox := fun n => tfmap f],
         where [Convert] stands for two arrows and the body writes one.  The
         slot it initialises is a [std::function] of the full signature, which
         no partial application can fill, so the arrows the name stands for are
         the arrows the body must have. *)
      let inner_body =
        Ml_type_util.eta_expand_to
          (Ml_type_util.expand_ml_fun_alias ml_ty)
          inner_body
      in
      begin_body ~owner:n ();
      (* The constant's own type is also the expected type of its body, so an
         IIFE standing in for a let-in tail expression re-bases onto it rather
         than onto nothing. *)
      let b_expr = with_region inner_body (fun () -> gen_constant_value ~expected_ty:ty_ir inner_body) in
      (* Wrap with std::any_cast when the C++ expression returns std::any but the
         declared type is concrete.  Two detection paths:
         (a) MLmagic — the extraction explicitly flagged a type coercion.
         (b) Record field projection — the field's return type is a promoted
             type var (erased to std::any) but Coq's type system sees the
             concrete type, so no MLmagic is generated. *)
      let is_concrete_target =
        match ty_ir with
        | Any | Variable _ | Obligation Unresolved_type | Void | Auto -> false
        | Entity_application (g, _, _) when Table.is_erased_type_const g -> false
        | _ -> not (type_is_erased_ir ty_ir)
      in
      let needs_any_cast =
        is_concrete_target
        && (has_magic || ml_body_returns_erased_field inner_body)
      in
      let b_expr =
        if needs_any_cast then unbox_value ty_ir b_expr
        else
          (* (c) The emitted expression is itself the evidence: a projection
             out of a pair that was recovered from a box hands back a
             [std::any] whatever its ML type says, and neither (a) nor (b)
             sees that. *)
          recover_boxed_component ty_ir b_expr
      in
      (* When a unit-typed constant's body may call a void-ified function,
         wrap in an IIFE that executes the body for side effects and
         returns Unit::e_TT.  Pure enum literals need no wrapping. *)
      let b_expr =
        if is_cpp_unit_type_ir ty_ir && ml_type_is_unit ml_ty then
          match b_expr with
          | Enum_value _ -> b_expr
          | Entity (_, _, Some ci) when ci.inline <> None -> b_expr
          | _ -> Cpp_ir.Build.iife None [Expression b_expr; Return (Some (mk_tt_expr ()))]
        else b_expr
      in
      let b_expr =
        match Translation_types.slot_repr_of_cpp_type_ir ty_ir with
        | Boxed kind -> box_for_any_slot kind inner_body b_expr
        | Native -> b_expr
      in
      (* A type naming a class field this scope cannot resolve would spell
         the field's file-scope erased alias, while the initialiser -- built
         through the instance the term names -- has the real type: [run :=
         @int_to_ptr natIPtr (@PIV natIPtr) ...] is an [EOU<pair<Nat, bool>>],
         not an [EOU<crane::obj>].  The initialiser says it. *)
      let ty_ir : Cpp_ir.Lowered.Type.t = if Translation_types.mentions_unresolved_promoted_ir ty_ir then Auto else ty_ir in
      (* A polymorphic constant's family parameter is plain, as a
         function's is, and written applied until deapplied. *)
      (templated (deapply_plain_tvars temps (variable n (Const ty_ir) b_expr)), empty_env ())
  in
  result

(** {!gen_spec__inner} with [n] as the declaration being generated. *)
let gen_spec n b ty =
  Table.with_decl_ref n (fun () -> gen_spec__inner n b ty)

(** Where a function's definition is written: a template's in the header,
    anything else's in the implementation file. *)
type definition_file = Header | Implementation

(** What generating a top-level term produced. *)
type generated_entity =
  | Defined of Cpp_ir.Lowered.Decl.t * definition_file
      (** a definition, and the file it is written in *)
  | Declared of Cpp_ir.Lowered.Decl.t  (** a declaration with no definition anywhere *)

(** A generated function, and what its file views are built from. *)
type generated_fun = {
  gf_entity : generated_entity;
  gf_env : env;  (** the environment its parameters were named in *)
  gf_lifted : Cpp_ir.Lowered.Decl.t list;  (** the helpers lifted out of its body *)
}

(** A template's definition goes in the header, anything else's in the
    implementation file. *)
let definition_file_of tvars = if tvars = [] then Implementation else Header

(** [d] as a definition, in the file its template variables [tvars] put it
    in. *)
let defined d tvars = Defined (d, definition_file_of tvars)

(** Generate each function of a mutually recursive group, translating each
    body once, then lower the group's control from its ControlIR where that
    is the bridge's to lower ({!Control_to_cpp_ir}). *)
let gen_dfuns_dual fds =
  let generated =
    List.map
      (fun {fd_ref; fd_body; fd_type} -> collecting_lifted (fun () -> gen_dfun_def fd_ref fd_body fd_type))
      fds
  in
  let lowered = Control_to_cpp_ir.lower_group (List.map (fun ((ds, _, _), _) -> ds) generated) in
  List.map2
    (fun ds ((_, env, tvars), lifted) -> {gf_entity = defined ds tvars; gf_env = env; gf_lifted = lifted})
    lowered generated

(** Generate a single Dterm function, translating its body once. *)
let gen_decl_for_pp_dual__inner n b ty =
  let (gf_entity, gf_env), gf_lifted =
    collecting_lifted @@ fun () ->
    match gen_decl_for_pp n b ty with
    | Some ds, env, tvars -> (defined ds tvars, env)
    | None, _, _ ->
      (* Not a function: a declaration, and no definition anywhere. *)
      let spec, env = gen_spec n b ty in
      (Declared spec, env)
  in
  {gf_entity; gf_env; gf_lifted}

(** {!gen_decl_for_pp_dual__inner} with [n] as the declaration being
    generated. *)
let gen_decl_for_pp_dual n b ty =
  Table.with_decl_ref n (fun () -> gen_decl_for_pp_dual__inner n b ty)
