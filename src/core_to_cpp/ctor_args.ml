(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The type side of a constructor application: the template arguments a
    constructor is drafted or expected at, which arguments store an erased
    function and how such a lambda is generated, and the type hint a
    constructor or coercion carries. *)

open Names
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query
open Base.Table

(** [core_ast_type_hint e] is the Core type [e] carries, when it carries one: a
    constructor's own annotation, or the source type of a coercion extraction
    inserted around it.  Used to recover a type argument left [Tunresolved] by
    extraction. *)
let rec core_ast_type_hint = function
  | Core.Expr.Construct {result_type = t; _} -> Some t
  | Core.Expr.Coerce {source_type = from; value = inner; _} ->
    ( match Base.Type_util.resolve_meta from with
    | Core.Type.Unknown | Core.Type.Erased _ -> core_ast_type_hint inner
    (* A function value's representation at a slot it is coerced into is the
       boxed one [crane_erase_fn] produces, never its own arrow type: grounding
       it would defeat the boxing and the consumer's fixed [any_cast]. *)
    | Core.Type.Arrow _ -> None
    | t -> Some t )
  | Core.Expr.Boxed_value {value = inner; _} | Core.Expr.Lambda_group_barrier {value = inner; _} ->
    core_ast_type_hint inner
  | _ -> None

(** [promoted_tys_of_arity n] is the concrete types the enclosing scope's
    promoted type variables stand for, when there are exactly [n] of them and
    so they can be read as the arguments of an [n]-ary type.  Erased entries
    are dropped, since a promoted variable that resolves to [std::any] says no
    more than the erased annotation it would replace. *)
let promoted_tys_of_arity cx n =
  match List.filter_map (fun (_, t) -> if Cpp_ir.Types.prints_as_any t then None else Some t)
          cx.ctx.lexical.promoted_var_map
  with
  | tys when List.length tys = n -> Some tys
  | _ -> None

(** When a lambda literal is about to be stored via [crane_erase_fn] (see the
    [core_expr_is_function_value] call site in the custom-constructor arg loop),
    the lambda will only ever be invoked with its whole argument boxed as a
    single raw [std::any] (never with the generically-deduced concrete type),
    because that is exactly what [crane_erase_fn]'s CTAD-non-viable fallback
    forwards. If the lambda's own bound parameter [n] is immediately
    pattern-matched via a custom (e.g. pair) match, that match must therefore
    treat the scrutinee as erased — wrap it in [Core.Expr.Boxed_value] so
    [gen_custom_cpp_case] emits [any_cast<pair<any,any>>(...)] instead of a
    structured binding directly on the (at runtime erased) parameter. Without
    this, a domain type that is a pair with a mix of erased/concrete fields
    (e.g. [S.sem a * unit]) renders the parameter as a generic [auto&], and the
    destructure compiles fine at the OCaml/template level but fails at C++
    instantiation time when [auto&] deduces to [std::any] (structured
    bindings are not valid on [std::any]). *)
let rec mark_own_param_for_pair_erasure n body =
  match body with
  | Core.Expr.Match {scrutinee_type = ty;
                     scrutinee = (Core.Expr.Bound_variable {index = i; _} as scrut);
                     branches = pv;
                     occurrence = occ} when i = n && is_custom_match pv ->
    Core.Expr.Match {scrutinee_type = ty;
                     scrutinee = Core.Expr.Boxed_value {value = scrut; occurrence = Core.Occurrence.fresh ()};
                     branches = pv;
                     occurrence = occ}
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
    Core.Expr.Coerce {source_type = from;
                      target_type = into;
                      value = mark_own_param_for_pair_erasure n a;
                      occurrence = mocc}
  | Core.Expr.Boxed_value {value = a; occurrence = mocc} ->
    Core.Expr.Boxed_value {value = mark_own_param_for_pair_erasure n a; occurrence = mocc}
  | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
    Core.Expr.Lambda_group_barrier {value = mark_own_param_for_pair_erasure n a; occurrence = mocc}
  | other -> other

(** [field_stores_erased_fn_value ~field_cpp_ty field_types i e] — true when
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
let field_stores_erased_fn_value ~(field_cpp_ty : Cpp_ir.Lowered.Type.t option) field_types i e =
  match List.nth_opt field_types i with
  | Some ft ->
    let field_is_abstract_var =
      match ft with Core.Type.Variable _ -> true | _ -> false
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
       || (result_is_erased && match strip_magic e with Core.Expr.Lambda _ -> true | _ -> false))
  | None -> false

(** The type arguments the enclosing function's return type supplies for the
    inductive [ind], when it names [ind] with exactly [arity] of them.

    A constructor call for an inductive with dependent parameters has to
    instantiate the same template its caller expects, and the return type is
    where that expectation is recorded.  Namespace and [shared_ptr] wrappers
    are seen through, as are typedefs, which may name [ind] only indirectly.
    [None] when the return type says nothing about [ind]. *)
let expected_type_args_from_return cx env ~ret ?slot ind ~arity =
  let rec go (cpp_ty : Cpp_ir.Lowered.Type.t) =
    match cpp_ty with
    | Entity_application (r, tys, _)
      when Names.GlobRef.CanOrd.equal ind r && List.length tys = arity ->
      Some tys
    | In_namespace (_, inner) | Shared_pointer inner -> go inner
    | Entity_application (_, tys, _) when List.exists (fun t -> go t <> None) tys ->
      List.find_map go tys
    | Entity_application (GlobRef.ConstRef kn, _, _) -> (
      match Base.Table.lookup_typedef_unchecked kn with
      | Some core_ty ->
        go (Types.cpp_of_core cx env core_ty)
      | None -> None )
    | _ -> None
  in
  match slot with
  | Some t when go t <> None -> go t
  | _ -> (
    match ret with
    | Some rt -> go rt
    | None -> None )

(** Whether argument [i] of constructor [r] is forwarded unboxed by the
    constructor's custom template ([%a<i>] and nothing else): a pure
    type-level erasure marker such as [sum1], with no field storage to box
    into. *)
let ctor_arg_is_passthrough r i =
  match r with
  | GlobRef.ConstructRef ((kn, mi), cidx) ->
    ( try
        let tmpl = List.nth (Base.Table.find_custom_ctor_templates (kn, mi)) (cidx - 1) in
        String.trim tmpl = Printf.sprintf "%%a%d" i
      with _ -> false )
  | _ -> false

(** The template arguments a custom constructor annotated [ty] is drafted
    at, before its destination refines them ({!Construction.gen_expr_custom_cons}):
    the inductive's parameters, converted, where every one erases the
    promoted types of [promoted_active]'s arity or, failing that, [return]'s
    arguments when it is the same inductive; an unresolved one written down as
    a box ({!Base.Type_util.materialise_opaque}). *)
let ctor_draft_temps cx env ~promoted_active ~(return : Cpp_ir.Lowered.Type.t option) (ty : Core.Type.t) =
  let temps =
    match ty with
    | Core.Type.Global_app {head = cn; type_arguments = raw_tys; _} ->
      let tys =
        match cn with
        | GlobRef.IndRef (kn, _) -> (
          match Base.Table.get_ind_num_param_vars_opt kn with
          | Some nv -> safe_firstn nv raw_tys
          | None -> raw_tys )
        | _ -> raw_tys
      in
      let temps = Types.template_params_of_core cx ~site:Through_tvar env tys in
      if List.for_all Cpp_ir.Types.prints_as_any temps && promoted_active then
        match promoted_tys_of_arity cx (List.length tys) with
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
  List.map materialise_opaque temps

(** Whether argument [e], at index [i] of constructor [r], is a function
    stored via [crane_erase_fn] into an erased field: the field is at a type
    parameter of the inductive ([field_tys], dummies dropped) whose template
    argument ([temps]) prints as [std::any], and the constructor's template
    does not forward the argument as it is. *)
let stores_erased_fn cx ?var env r ~field_tys ~(temps : Cpp_ir.Lowered.Type.t list) i e =
  match List.nth_opt field_tys i with
  | Some (Core.Type.Variable {variable = j; _}) -> (
    match List.nth_opt temps (j - 1) with
    | _ when ctor_arg_is_passthrough r i -> false
    | Some t when Cpp_ir.Types.prints_as_any (Types.unfold_cpp_typedef cx env t) ->
      Erasure.core_expr_is_function_value cx ?var e
    | _ -> false )
  | _ -> false

(** [e], a constructor argument {!stores_erased_fn} says is stored via
    [crane_erase_fn], as lowering generates it: a lambda is only ever invoked
    with its whole argument boxed as one [std::any] holding the fully erased
    representation ([pair<any,any>] for a pair domain), so a custom match on
    its own parameter reads the scrutinee as erased
    ({!mark_own_param_for_pair_erasure}); a parameter whose type converts with
    no erased position -- a literal index picking a concrete branch of a type
    family -- is erased to [std::any] so that the cast on it compiles. *)
let erased_fn_lambda cx env e =
  match strip_magic e with
  | Core.Expr.Lambda {parameter = id; parameter_type = ty; body} ->
    if Base.Type_util.has_tany_in_type (Types.cpp_of_core cx env ty) then
      Core.Expr.Lambda {parameter = id; parameter_type = ty; body = mark_own_param_for_pair_erasure 1 body}
    else Core.Expr.Lambda {parameter = id;
                           parameter_type = Core.Type.Unknown;
                           body = mark_own_param_for_pair_erasure 1 body}
  | _ -> e
