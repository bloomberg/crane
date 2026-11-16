(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Call planning for translation: the plan a call to a global is written
    against ({!callee_abi}), the template arguments it writes -- dictionary
    carriers, higher-kinded and lifted-call arguments, families an instance
    fixes -- the position each argument is generated into, and the lowered
    call.  Also how a global use is curried to an expected type. *)

open Common
open Names
open Core_util
open Util
open Translation_state
open Type_util
open Core_query
open Table

module IntSet = Escape.IntSet

(** What a call to a global is, before its arguments are generated: the call
    as Core elaborated it, and what planning its C++ added; see
    {!plan_call}. *)
type call_plan = {
  instantiated : Elaborated_call.instantiated;
      (** The call's semantic half, decided before any of the C++ below. *)
  expected_result : Cpp_ir.Lowered.Type.t option;
      (** The C++ type the call is expected to produce: the position's, with
          a family it erased refined from what the arguments state, or, where
          the position states none, the arguments' or the enclosing
          function's return type. *)
  instance_type_args : Cpp_ir.Lowered.Type.t option list;
      (** The template argument each class-instance argument is passed as. *)
  instance_families : (Cpp_ir.Lowered.Type.t * Id.t list * (Id.t * Cpp_ir.Lowered.Type.t) list) list;
      (** The families the call's instances were found to have
          ({!instance_family_binding}); the slots their
          arguments are generated against erase them the same way. *)
  tvars : Id.t list;
      (** The enclosing declaration's type variable names. *)
  concrete_tvar_type : Cpp_ir.Lowered.Type.t option;
      (** For a call with no written type arguments and excess value
          arguments, the concrete type of its polymorphic result: the excess
          arguments' types to the enclosing function's return type. *)
  instance_promoted : (Id.t * Cpp_ir.Lowered.Type.t) list;
      (** Promoted variables bound to concrete C++ types by the concrete
          instances the call passes, so that constructors in its arguments
          use those types instead of [std::any]. *)
  result_tvar_map : (Id.t list * (Id.t * Cpp_ir.Lowered.Type.t) list) Lazy.t;
      (** The callee's variables as the call's expected result instantiates
          them, read for a parameter the substitution left erased. *)
}

(** Checks the plan [abi] of a function against [live], the C++ type of its
    declared Core type as a call site rebuilds it: the plan declares one value
    parameter per domain other than a class dictionary or a skipped type, and
    one dictionary template parameter per dictionary domain.  Its types are
    not compared: the declaration spells its parameters after its head's
    relaxations, through its instances' associated types and with aliases
    expanded, so they differ from the type rebuilt here by design. *)
let check_planned_arity abi (live : Cpp_ir.Lowered.Type.t) =
  if Probe.checking () then
    match Callable_abi.signature abi with
    | None -> ()
    | Some {Callable_abi.params; _} ->
      let doms = match live with Function (d, _) -> d | _ -> [] in
      let dicts, values = List.partition Type_util.is_typeclass_type_cpp doms in
      let values = List.filter (fun t -> not (is_skipped_cpp_type t)) values in
      let instances =
        List.length
          (List.filter
             (fun p ->
               match p.Callable_abi.origin with Callable_abi.From_instance _ -> true | _ -> false )
             (Callable_abi.template_head abi) )
      in
      if List.length values <> List.length params || List.length dicts <> instances then
        Probe.violation "callable ABI"
          Pp.(
            str "the plan of " ++ GlobRef.print (Callable_abi.callee abi)
            ++ str (Printf.sprintf " declares %d value parameters and %d dictionaries" (List.length params) instances)
            ++ str (Printf.sprintf " where its type has %d and %d" (List.length values) (List.length dicts)) )

(** {!check_planned_arity} for the installed plan of [id], where it has one. *)
let check_installed_arity id live =
  if Probe.checking () then Option.iter (fun abi -> check_planned_arity abi live) (Callable_abi.lookup id)

(** {!instantiate_at_call} at the type arguments [use] wrote, read by the
    callee's scheme variables. *)
let instantiate_use_at_call (use : Core.Global_use.t) value_args ty =
  Core_util.instantiate_written ~reader:"instantiate_use_at_call" use
    (with_dict_carrier ~lex:(current_lexenv ()) ~caller:!Table.current_decl_ref use.callee
       value_args ty )

(** What an application of a global yields, as a Core type.

    The callee's declared type says it, once instantiated the way the call
    instantiates it: [tys] for its own [forall]s, and the dictionary argument
    for the class parameter its parameter types spell as the carrier applied.
    Both substitutions are {!instantiate_use_at_call}'s; this reads the
    codomain of the result.

    [None] where the callee has no recorded type, or fewer value arrows than
    the call has value arguments -- a partial application returns a function,
    which is not what the callers of this want. *)
let core_app_result_type (f : Core.Expr.t) (args : Core.Expr.t list) : Core.Type.t option =
  let ( let* ) = Option.bind in
  match f with
  | Core.Expr.Global ({callee = id; _} as use) ->
    let value_args =
      List.filter (function Core.Expr.Erased_value _ -> false | _ -> true) args
    in
    let* ty = find_type_opt id in
    Type_util.core_codomain_after (List.length value_args)
      (instantiate_use_at_call use value_args ty)
  | _ -> None

(** The variable {!Plan_templates.relax_tt_applied_return} takes out of [id]'s
    template head, if any: the higher-kinded head of an applied codomain that
    only a callback's result otherwise names -- [case_]'s [M] in [M X], which
    the declaration spells [std::invoke_result_t<F0 &, ...>] instead.  Read off
    the Rocq type for the reason {!writable_tvar_count} is. *)
let relaxed_tt_return_var id =
  match find_type_opt id with
  | None -> None
  | Some core_ty -> (
    match resolve_meta (core_codomain core_ty) with
    | Core.Type.Variable_app {head = h; arguments = [ _ ]}
      when IntSet.mem h (declared_higher_kinded_tvars core_ty) ->
      let occurs t = IntSet.mem h (collect_tvars_set IntSet.empty t) in
      let doms = List.map resolve_meta (core_domains core_ty) in
      (* A callback's result, written as an arrow; a definitional class
         spells its variable in the declaration's parameter list and so names
         it ([MonadIter<T1>]). *)
      let under_arrow d =
        match d with Core.Type.Arrow _ -> true | _ -> false
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
  let* core_ty = find_type_opt id in
  let n = Core_util.type_maxvar (type_simpl core_ty) in
  let occurs v t = IntSet.mem v (collect_tvars_set IntSet.empty t) in
  let cod = resolve_meta (core_codomain core_ty) in
  (* Only a codomain that {e applies} a variable is relaxed.  [list B] names
     [B] as a plain leading parameter that the call still has to write, and
     dropping it would leave nothing to deduce it from; [T V] is the
     higher-kinded shape {!Plan_templates.relax_applied_return} rewrites. *)
  (* And only a higher-kinded head: a family's application is written plain,
     which the declaration does not relax ({!Plan_templates.relax_applied_return}). *)
  let applied_cod =
    match cod with
    | Core.Type.Variable_app {head = h; _} ->
      IntSet.mem h (Type_util.higher_kinded_core_tvars [core_ty])
    | _ -> false
  in
  let derived v =
    applied_cod && occurs v cod
    && List.for_all
         (fun d ->
           match resolve_meta d with
           | Core.Type.Arrow _ -> true
           | d -> not (occurs v d) )
         (core_domains core_ty)
    && List.exists (fun d -> occurs v d) (core_domains core_ty)
  in
  (* Only a derived {e suffix} may be dropped.  A derived position followed by
     one that is still written cannot be removed without taking that one with
     it, and the later position may be doing work the truncation would undo --
     [iter]'s [R] is derived but its [I] is not, and dropping both loses an
     argument deduction was relying on the first two to place.  Where the list
     cannot be fixed by cutting its tail, it is left exactly as it was. *)
  let rec suffix_start v = if v < 1 then 1 else if derived v then suffix_start (v - 1) else v + 1 in
  Some (suffix_start n - 1)

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
    | Core.Type.Arrow _ -> true
    | Core.Type.Meta {contents = Some t} -> is_arrow t
    | _ -> false
  in
  (not (Table.is_custom x)) && not (is_arrow orig)

(** A singleton class's dictionary at the head of a call: the instance
    parameter it is, the class, and the class's one method, as the
    traversal's environment reads it.  Emission takes Core's reading
    ({!Core_elaborate.singleton_dictionary_call}) and checks it against this
    one. *)
let singleton_dictionary env head =
  match strip_magic head with
  | Core.Expr.Bound_variable {index = i; _} -> (
    match (Common.get_db_name_opt i env, get_env_type_opt i) with
    | Some id, Some (Core.Type.Global_app {head = c; _}) when Common.is_tc_instance_id id ->
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

(** Convert Core type arguments to C++ template parameters, applying type
    simplification and handling out-of-scope type variables.

    This function maps a list of Core types to C++ types for use in template
    argument lists. It performs two key transformations:

    1. Type simplification via [type_simpl] to normalize Core types
    2. Conversion to C++ types via [convert_core_type_to_cpp_type]
    3. Detection and erasure of unbound type variables

    The [tvars] parameter specifies the type variables in scope (as a list of
    typename declarations in the current C++ context). When a [Core.Type.Variable] appears
    with [None] for its binding and [tvars] is non-empty, this indicates the
    type variable index is out of scope — it references a typename that doesn't
    exist in the current C++ context.

    Out-of-scope type variables are marked as [dummy_type], which triggers
    [filter_erased_type_args] to drop the entire type argument list. This is
    safer than emitting invalid C++ like [template<typename T> ... U] where
    [U] is undefined.

    Example scenario where this occurs:
    - Core function with type scheme [forall A B, A -> B -> option A]
    - Partial application instantiates [A] but leaves [B] polymorphic
    - C++ code generator enters context with only [typename A]
    - Type arg list includes [Core.Type.Variable 2] for [B]
    - [convert_core_type_to_cpp_type] returns [Core.Type.Variable(2, None)] (no binding)
    - We mark it [dummy_type] to trigger erasure

    @param env   Translation environment (unused in current implementation)
    @param tvars Type variables in scope (C++ typename parameters)
    @param tys   Core type arguments to convert
    @return List of C++ types, with out-of-scope Tvars marked as dummy_type *)

(** Whether a bare reference to global [x] must be spelled [x()]: it is
    declared as a zero-parameter function rather than a data member.  That is
    the case for thunked values (monadic definitions, cofixpoints, extracted
    axioms) and for definitions that really do take C++ parameters.

    A Core arrow is {i not} enough: a definition all of whose arguments are
    erased (a lemma-only argument, say) converts to a non-function C++ type
    and is emitted as a data member by {!Gen_decls.gen_spec}.  Asking the
    converter is what keeps the two in step. *)
let glob_is_nullary_function x =
  match callee_core_type x with
  | None -> false
  | Some core_ty ->
    Translation_suspension.thunk_reason x <> None
    || ( match Translation_types.cpp_ir_of_core_type (empty_env ()) [] core_ty with
       | Function _ -> true
       | _ -> false )

(** The global [x], spelled [cglob], applied to [args]: a call, except that a
    global value referenced bare stays a value ({!glob_is_nullary_function}). *)
let apply_global x (cglob : Cpp_ir.Lowered.Expr.t) args =
  if args = [] && not (glob_is_nullary_function x) then cglob else Cpp_ir.Build.call cglob args

(** The site a callee's {e result} is spelled at ({!Cpp_ir.Types.arrow_site}): a
    codomain that is a type variable takes its C++ shape from the template
    argument instantiating it, so it is curried; one the declaration writes
    out is flat there. *)
let codomain_site core_ty : Cpp_ir.Types.arrow_site = if core_codomain_is_tvar core_ty then Through_tvar else Declared

(** {!codomain_site} for a call to the global [id].  An inline custom
    constant has no template argument: what it yields is whatever its text
    reads -- [fst]'s [%a0.first] is the pair's component, stored flat. *)
let call_result_site id : Cpp_ir.Types.arrow_site =
  if is_inline_custom id then Declared
  else match find_type_opt id with Some core_ty -> codomain_site core_ty | None -> Declared

(** [result_cpp_via_receiver env callee_ty args] is the C++ type a call's
    result really has, where the callee's declared codomain is one of the type
    variables its first argument's type instantiates -- the field a projection
    out of a dependent pair hands back, say.

    The answer is read off the {e converted} receiver, at the template position
    the codomain occupies in it.  Converting the codomain's own instantiation
    instead is not the same thing: a type argument that the receiver's
    conversion erases still spells concretely in isolation, and the field it
    describes is then physically a [std::any] while its Core type denies it.
    [None] means the call is not of this shape, or that the two spellings of
    the receiver disagree on how many arguments it has -- the position would
    then name the wrong one. *)
let result_cpp_via_receiver env callee_ty args : Cpp_ir.Lowered.Type.t option =
  let var_index t = match resolve_meta t with Core.Type.Variable {variable = j; _} -> Some j | _ -> None in
  let position_of j formals =
    let rec find i = function
      | [] -> None
      | f :: rest -> if var_index f = Some j then Some i else find (i + 1) rest
    in
    find 0 formals
  in
  (* The template arguments of [t], through references and pointers. *)
  let rec template_args_ir t =
    match unqualify_ty t with
    | Reference (_, t) | Pointer t | Shared_pointer t -> template_args_ir t
    | Entity_application (_, args, _) | Named (_, args) | External (_, args) | Apply (_, args) -> Some args
    | _ -> None
  in
  match (var_index (core_codomain callee_ty), core_value_domains callee_ty, args) with
  | Some j, dom0 :: _, arg :: _ -> (
    match (resolve_meta dom0, Option.map resolve_meta (infer_core_body_type arg)) with
    | Core.Type.Global_app {head = g1;
                            type_arguments = formals; _},
                              Some (Core.Type.Global_app {head = g2; type_arguments = actuals; _} as recv)
      when Common.globref_equal g1 g2 -> (
      match (position_of j formals, template_args_ir (Translation_types.cpp_of_core env recv)) with
      | Some i, Some cpp_args when List.length actuals = List.length cpp_args ->
        List.nth_opt cpp_args i
      | _ -> None )
    | _ -> None )
  | _ -> None

(** The template name a written type [c] stands for at a higher-kinded
    variable: [c] itself as a constructor, unless applying it changes
    nothing -- [fun T => list nat], which extraction writes as its body
    [list nat] -- when it is the constant one, [crane::constant_tc<c>::c]. *)
let carrier_template env tvars c : Cpp_ir.Lowered.Type.t =
  let carrier = Translation_types.template_arg_of_core_type ~site:Through_tvar env tvars c in
  let constant = Core_util.eq_core_type (Core_util.apply_core_type c [Core.Type.Unknown]) c in
  Type_constructor
    (if constant then Member (External (Crane_rt.constant_tc, [carrier]), Id.of_string "c") else carrier)

(** The explicit type arguments a call needs when the callee is generic in a
    type {e constructor} and Rocq erased which one.

    A higher-kinded class parameter reaches the call as [Core.Type.Erased]: the carrier
    of [TFunctor (fun T => T * box T)] is a term Rocq computed away.  C++
    deduces the parameter from the value argument instead, by matching
    [T1<T2>] against the argument's type -- which works exactly when the
    carrier is a template name applied to one argument, and fails outright
    when it is not: [std::pair<Nat, Box<Nat>>] deduces [T1 = std::pair], a
    binary template where a unary one was declared.

    The carrier is recovered from the type the result is expected to have.
    The callee returns [Core.Type.Variable_app (p, [Core.Type.Variable v])] -- the carrier at position [p]
    applied to the variable at position [v] -- so abstracting the expected
    result over whatever [v] was instantiated to inverts that application.
    {!Translation_tvars.abstract_cpp_type} writes the sentinel the printer mints an
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
    ({!Core_util.apply_core_type}), and has no template to name: it is the type
    function {!Crane_rt.constant_tc} makes of it. *)
let hkt_carrier_type_args env tvars ?result id tys =
  Probe.changed "REPAIR_hkt_carrier_type_args" id ~before:None @@
  let ( let* ) = Option.bind in
  let* core_ty = find_type_opt id in
  match Core_util.Var_types.find_tvar tys 1 with
  | Some c
    when IntSet.mem 1 (Type_util.higher_kinded_core_tvars [core_ty])
         && not (Core_util.is_erased_type (resolve_meta c))
         && not (core_type_contains_erased c) ->
    Some [carrier_template env tvars c]
  | _ ->
  let* p, v =
    match resolve_meta (core_return_type core_ty) with
    (* Only a leading carrier is written: an explicit argument list is
       positional, so a carrier further in would need every argument before it
       spelled as well, and a class parameter is always quantified first. *)
    | Core.Type.Variable_app {head = 1; arguments = [Core.Type.Variable {variable = v; _}]} -> Some (1, v)
    | _ -> None
  in
  let* () =
    match Core_util.Var_types.find_tvar tys p with
    | Some (Core.Type.Erased _) -> Some ()
    | _ -> None
  in
  let* v_core = Core_util.Var_types.find_tvar tys v in
  let* result =
    match result with
    | None -> current_cpp_return_type ()
    | r -> r
  in
  let over = Translation_types.template_arg_of_core_type ~site:Through_tvar env tvars v_core in
  let* carrier = Translation_tvars.abstract_cpp_type ~over result in
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
    discarded.  [binder_ty] is the lifted thing's own Core type, whose codomain
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
let lifted_call_type_args
    ~(class_args : Cpp_ir.Lowered.Type.t list) ~env ~outer_tvars ~head ~all_tvar_names ~binder_ty ~param_core_tys :
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
      match Translation_types.cpp_ir_of_core_type env all_tvar_names binder_ty with
      | Function (_, cod) -> cod
      | t -> t
    in
    let tvar_map =
      match current_cpp_return_type () with
      | Some conc_ret -> extract_tvar_map tmpl_cod conc_ret
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
              match current_cpp_return_type () with
              | Some ret_ty -> ret_ty
              | None -> Cpp_ir.Build.named_variable tvar_name ) )
          extra_tvar_names
    in
    let deducible =
      List.concat_map
        (fun core_ty ->
          get_tvars (Translation_types.cpp_ir_of_core_type env all_tvar_names core_ty) )
        param_core_tys
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
    sources end at a Core type headed by the carrier, and are consumed as one.

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
    dict_carrier_core_type ~lex:(current_lexenv ()) ~caller:!Table.current_decl_ref id args
  in
  (* Abstracted over the traversed type, as {!Translation_tvars.apply_hkt_tyctors} does: the
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
     the carrier recovery declined to fill is left as the [Core.Type.Variable_app] it was, and by
     then nothing tells it apart from one that was recovered; writing it out
     spells a carrier built partly from a class parameter that is in scope and
     is not the one meant.  There the leading argument is abstracted over as
     before, which yields the outer head alone -- still wrong, but wrong the
     way deduction is wrong, and absorbed wherever a converting constructor
     absorbs it.  A wrong spelling is worse than an unrecovered one.

     Only occurrences among the {e arguments} count.  The head may be a [Core.Type.Variable_app]
     and be right: a carrier that {e is} a class parameter is written as that
     parameter, which the enclosing declaration has in scope. *)
  let rec unrecovered t =
    match resolve_meta t with
    | Core.Type.Variable_app _ -> true
    | Core.Type.Global_app {type_arguments = targs; _} -> List.exists unrecovered targs
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
    match resolve_meta t with
    | Core.Type.Unknown | Core.Type.Variable _ -> true
    | Core.Type.Global_app {type_arguments = targs; _} | Core.Type.Variable_app {arguments = targs; _} ->
      List.exists mentions_traversed targs
    | Core.Type.Arrow {parameter = a; result = b} -> mentions_traversed a || mentions_traversed b
    | _ -> false
  in
  let rec traversed t =
    match resolve_meta t with
    | Core.Type.Global_app {type_arguments = (t0 :: _ as targs); _}
    | Core.Type.Variable_app {arguments = (t0 :: _ as targs); _} ->
      (* No argument mentioning it means there is nothing better to say than
         what the leading one says, which is what this did before. *)
      traversed (Option.default t0 (List.find_opt mentions_traversed targs))
    | t -> t
  in
  let* over =
    match resolve_meta cod with
    | Core.Type.Global_app {type_arguments = (t0 :: _ as targs); _}
    | Core.Type.Variable_app {arguments = (t0 :: _ as targs); _} ->
      let whole = if List.exists unrecovered targs then t0 else traversed cod in
      Some (Translation_types.template_arg_of_core_type ~site:Through_tvar env tvars whole)
    | _ -> None
  in
  let* carrier =
    Translation_tvars.abstract_cpp_type ~over
      (Translation_types.template_arg_of_core_type ~site:Through_tvar env tvars cod)
  in
  Some [(Type_constructor carrier : Cpp_ir.Lowered.Type.t)]

(** The type of the global [use] names, at the type arguments the use wrote.
    An adapter's parameters are spelled in the caller's scope, so the
    callee's own type variables must not survive into them: this site's type
    arguments are what they stand for. *)
let instantiated_type (use : Core.Global_use.t) =
  Option.map
    (Core_util.instantiate_written ~reader:"instantiated_type" use)
    (callee_core_type use.callee)

(** {!Translation_coerce.curry_value_to_expected} for the global [use] names. *)
let curry_to_expected env ?expected_ty (use : Core.Global_use.t) cglob =
  let decl_ty = callee_core_type use.callee in
  let core_ty = instantiated_type use in
  let callee_site =
    let live = Option.map (Translation_types.cpp_of_core env) decl_ty in
    if Probe.checking () then
      Option.iter (fun t -> check_installed_arity use.callee t) live;
    match live with
    | Some (Function (dom, _)) -> Cpp_ir.Types.Declared_at (List.length dom)
    | _ -> Cpp_ir.Types.Declared
  in
  Translation_coerce.curry_value_to_expected env ?expected_ty ~callee_site core_ty cglob

(** The plan a call of the class field [x] through a concrete instance is
    written against.  The instance declares each method as a member template
    over the method's own type variables -- the class's parameters are the
    instance, not parameters of its methods -- so the plan keeps the
    variables whose binders come after the class's. *)
let projection_abi x =
  let n_class = Type_util.projection_class_arity x in
  let of_method v =
    match Option.bind (Core_util.recorded_schema x) (fun s -> Core.Schema.origin s v) with
    | Some b -> Scheme.Binder.position b.Core.Schema.binder >= n_class
    | None -> true
  in
  Callable_abi.foreign ~callee:x ~scheme:(Core_util.reference_scheme x) ~kept:of_method ()

(** The plan a call to [id] is written against: the head [id] was declared
    with, or, where it is not generated here, the conventions its call sites
    assume -- [instances] dictionaries first, then the variables it keeps up
    to the last one a call can reach, the leading phantoms among them, each
    at the kind its type demands. *)
let callee_abi ~instances id =
  let core_ty = find_type_opt id in
  let hk = Option.cata declared_higher_kinded_tvars IntSet.empty core_ty in
  let relaxed_tt = relaxed_tt_return_var id in
  let omitted = Translation_tvars.type_arg_omission id in
  Callable_abi.plan id ~scheme:(Core_util.reference_scheme id) ~instances ~omitted
    ~higher_kinded:(fun v -> IntSet.mem (Scheme.Var.ordinal v) hk)
    ~kept:(fun v -> omitted v = None && relaxed_tt <> Some (Scheme.Var.ordinal v))
    ?reachable:(writable_tvar_count id)
    ~relaxed:(fun i ->
      IntSet.mem i (Option.cata Type_util.relaxed_higher_kinded_tvars IntSet.empty core_ty) )
    ~phantom_prefix:(Translation_types.leading_phantom_count id)

(** The explicit template arguments of a reference to [id] that is given a
    value for some of its variables, [by_var] pairing each variable with its
    C++ type: planned against [id]'s head, no dictionary among them. *)
let written_at_variables id (by_var : (int * Cpp_ir.Lowered.Type.t) list) =
  Template_application.to_list
    (Template_application.plan (callee_abi ~instances:0 id)
       ~instance:(fun _ -> None)
       ~scheme:(fun v -> List.assoc_opt (Scheme.Var.ordinal v) by_var) )

(** A call lowered against its callee's plan: the plan its arguments are
    lowered by, the callee's C++ type at the call, the written type arguments by
    scheme variable after the evidence stage, the callee's ABI and the
    template application planned against it, and each scheme variable's
    written C++ type. *)
type lowered_call = {
  callee : GlobRef.t;
  plan : call_plan;
  callee_type : Cpp_ir.Lowered.Type.t;
  written : Core_util.Var_types.t;
  abi : Callable_abi.t;
  application : Template_application.t;
  written_by_var : (Scheme.Var.t * Cpp_ir.Lowered.Type.t) list;
}

(** [call_type_args ~caller ?expected_ty env id plan args] -- the type
    arguments a call to [id] from the declaration [caller] writes, given its
    generated arguments: the dictionaries'
    first, then the regular ones that survive the erasure filters, recovered
    from the expected result, a dictionary or an argument where the filters
    left nothing.  Also the callee's instantiated C++ type and the
    instantiation the type arguments were read from, which the assembly
    needs. *)
let call_type_args ~caller ~lex ?(expected_ty : Cpp_ir.Lowered.Type.t option) env id plan ~has_value_args =
  let args = if has_value_args then [()] else [] in
  let {
    instantiated =
      {
        Elaborated_call.call =
          {Elaborated_call.primary = primary_core_args; regular = regular_core_args; _} as call;
        reading = tyargs;
        callee_type_at_call = fn_core_ty_subst;
        params = fn_param_core_tys;
        params_orig = fn_param_core_tys_orig;
        subst_index_of_orig;
        _
      };
    instance_type_args = typeclass_type_args;
    tvars = tvars;
    concrete_tvar_type = concrete_tvar_type;
    result_tvar_map = result_tvar_map;
    _
  } = plan in
  let leading_params = Elaborated_call.leading_params call in
  let dictionary_filled = Elaborated_call.dictionary_filled call in
  (* The callee's variable its type spells [Core.Type.Variable (_, i)]. *)
  let scheme_var i =
    Option.bind (Core_util.reference_scheme id) (fun s -> Scheme.Var.of_tvar s i)
  in
  (* Whether [v] comes from a type binder of the callee's that erasure
     removed, as its schema records: what the call would pass there is a
     type, and nothing is passed. *)
  let schema = Core_util.recorded_schema id in
  let erased_type_binder v =
    match Option.bind schema (fun s -> Core.Schema.origin s v) with
    | Some {Core.Schema.role = Core.Schema.Erased Core.Erasure_reason.Type_argument; _} -> true
    | _ -> false
  in
  let ty = Translation_types.cpp_of_core env fn_core_ty_subst in
  (* Combine: instance types first, then regular type args. If any regular
     type arg is Tany or a dummy type glob (from erased params), drop ALL
     regular type args via filter_erased_type_args and let the compiler deduce
     them. See filter_erased_type_args for why we must drop all args rather
     than just the erased ones.

     Exception: when the callee's return type depends on an erased type var,
     C++ can't deduce it from lambda arguments (lambdas don't participate in
     template argument deduction). In that case, recover the concrete type
     from the enclosing function's return type. *)
  (* A partial application writes only the type arguments the Rocq term
     applied: [Instance Fun_Mon := { ffmap := @liftM m _ }] names the
     carrier and leaves [liftM]'s own element variables to inference, which
     in OCaml costs nothing and in C++ costs everything -- they occur only
     in [typename I::m<T>] and in the return type, both non-deduced.  The
     arguments still say what they are, so resolve them from those. *)
  let tyargs = resolve_from_argument_types ~lex tyargs primary_core_args in
  let tys = Call_tyargs.by_variable tyargs in
  (* The whole list is built as a function of the reading because it may
     have to be built twice: what a call writes is decided by the erasure
     filters, and the recoveries below run only where they left nothing.  A
     pass that resolves one variable would otherwise silently disable them. *)
  let build_type_args tyargs =
  let tys = Call_tyargs.by_variable tyargs in
  (* The callee's variables it applies and still declares plain: a carrier
     it writes at the erased element ([Iter M]'s [M] is [T1], standing for
     [M<crane::obj>]). *)
  let plain_carriers =
    match find_type_opt id with
    | Some core_ty ->
      let hk = declared_higher_kinded_tvars core_ty in
      (* A class's carrier -- the argument of a definitional class in a
         domain, [TFunctor T] -- and not a family, which is applied at an
         index its struct already leaves out. *)
      let class_carriers =
        List.fold_left
          (fun acc d ->
            match resolve_meta d with
            | Core.Type.Global_app {head = (GlobRef.ConstRef _ as g); type_arguments = [ a ]; _}
              when Typeclasses.is_class g -> (
              match resolve_meta a with
              | Core.Type.Variable_app {head = i; _} | Core.Type.Variable {variable = i; _} -> IntSet.add i acc
              | _ -> acc )
            | _ -> acc )
          IntSet.empty (core_domains core_ty)
      in
      Hashtbl.fold
        (fun i _ acc ->
          if IntSet.mem i hk || not (IntSet.mem i class_carriers) then acc
          else IntSet.add i acc )
        (Type_util.applied_core_tvar_arities [core_ty])
        IntSet.empty
    | None -> IntSet.empty
  in
  (* Whether the caller applies its variable [j]: a type constructor,
     whatever its declaration made of it -- a class carrier, a template
     name, or a family written plain, which applied is itself again. *)
  let caller_higher_kinded j =
    match caller with
    | Some r -> (
      match find_type_opt r with
      | Some caller_ty ->
        Hashtbl.mem (Type_util.applied_core_tvar_arities [caller_ty]) j
      | None -> false )
    | None -> false
  in
  (* A carrier the declaration writes plain -- [TFunctor T]'s [T], whose
     applications [T U] and [T V] are both the one [T1] -- is bound off the
     result whole, and the result has the element at the call's own [V].
     The declaration's [T1] stands for the carrier at the erased element --
     it is what the dictionary is spelled at, and the parameters and result
     read it at their elements through [crane::rebind_t] -- so the element
     is erased out of it. *)
  let erase_carrier_elements i t' =
    match find_type_opt id with
    | Some core_ty when IntSet.mem i plain_carriers ->
      let rec elements acc t =
        match resolve_meta t with
        | Core.Type.Variable_app {head = k; arguments = args} ->
          let acc = if k = i then args @ acc else acc in
          List.fold_left elements acc args
        | Core.Type.Global_app {type_arguments = args; _} -> List.fold_left elements acc args
        | Core.Type.Arrow {parameter = a; result = b} -> elements (elements acc a) b
        | _ -> acc
      in
      let element_args = elements [] (core_codomain core_ty) in
      let element_tys =
        List.filter_map
          (fun a ->
            match resolve_meta a with
            | Core.Type.Variable {variable = j; _} -> (
              match Core_util.Var_types.find_tvar tys j with
              | Some ty when not (Core_util.is_erased_type (resolve_meta ty)) ->
                let c = Translation_types.template_arg_of_core_type ~site:Cpp_ir.Types.Through_tvar env tvars ty in
                if Cpp_ir.Types.prints_as_any c then None else Some c
              | _ -> None )
            | _ -> None )
          element_args
      in
      (* An element the declaration itself erased -- a method's own
         quantifier, [option (F U)] at [U] gone -- is nowhere in what the
         result binds, so a binding that erases nothing is some
         application of the carrier, not the carrier: nothing here can
         tell which part is the element. *)
      let element_erased_by_declaration =
        List.exists
          (fun a ->
            match resolve_meta a with
            | Core.Type.Variable _ -> false
            | _ -> true )
          element_args
      in
      if element_tys = [] then
        if element_erased_by_declaration
           && not (Type_util.has_tany_written t')
        then None
        else Some t'
      else
        (* Compared unqualified: the same type reaches here spelled
           through its wrapper struct and without it. *)
        let rec norm t =
          Cpp_ir.Types.map
            (fun (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
              match t with
              | In_namespace (_, t) | Const t -> norm t
              | Any | Obligation Opaque_type | Variable (Index (_, None)) -> Any
              | Variable (Index (_, Some n) | Named n)
                when not (List.exists (Id.equal n) (!tctx).lexical.current_type_vars) ->
                Any
              | t -> t )
            t
        in
        let element_tys = List.map norm element_tys in
        let t'' =
          Cpp_ir.Types.map
            (fun t -> if List.mem (norm t) element_tys then (Any : Cpp_ir.Lowered.Type.t) else t)
            t'
        in
        Some t''
    | _ -> Some t'
  in
  (* A plain carrier the call erased may still be stated by the dictionary
     it is handed: [TFunctor_outer1]'s [h0 :
     TFunctor<two<std::any, T1>>] is the carrier its [tfmap] call is at,
     already at the erased element. *)
  let carrier_from_dictionary i =
    let unwrap = Cpp_ir.Types.strip_param_spelling in
    List.find_map
      (fun (k, pt) ->
        match resolve_meta pt with
        | Core.Type.Global_app {head = (GlobRef.ConstRef _ as g); type_arguments = [a]; _}
          when Typeclasses.is_class g
               && ( match resolve_meta a with
                  | Core.Type.Variable_app {head = i'; _} | Core.Type.Variable {variable = i'; _} -> i' = i
                  | _ -> false ) -> (
          (* What the call instantiated the class at, where that is known:
             the carrier composed and applied at the erased element. *)
          let from_instantiation =
            match subst_index_of_orig k with
            | Some ks -> (
              match Option.map resolve_meta (Param_pos.nth fn_param_core_tys ks) with
              | Some (Core.Type.Global_app {head = g'; type_arguments = [x]; _})
                when GlobRef.UserOrd.equal g g'
                     && not
                          (let rec has_class t =
                             match resolve_meta t with
                             | Core.Type.Global_app {head = h; type_arguments = l; _} ->
                               Typeclasses.is_class h || List.exists has_class l
                             | Core.Type.Arrow {parameter = a; result = b} -> has_class a || has_class b
                             | Core.Type.Variable_app {arguments = l; _} -> List.exists has_class l
                             | _ -> false
                           in
                           has_class x) ->
                let c = Translation_types.template_arg_of_core_type ~site:Cpp_ir.Types.Through_tvar env tvars x in
                (* A carrier is written at the erased element, so an
                   instantiation that erases nothing is some application
                   of it, not the carrier. *)
                ( match erase_carrier_elements i c with
                | Some c
                  when (not (Cpp_ir.Types.prints_as_any c))
                       && Type_util.has_tany_written c ->
                  Some c
                | _ -> None )
              | _ -> None )
            | None -> None
          in
          match from_instantiation with
          | Some _ as c -> c
          | None ->
          match
            Option.bind
              (Param_pos.regular_of ~leading:leading_params k)
              (List.nth_opt regular_core_args)
          with
          | Some arg -> (
            match strip_magic arg with
            | Core.Expr.Bound_variable {index = j; occurrence = occ} -> (
              match
                Option.map unwrap
                  (Translation_binders.planned_binder_type_or_derive ~use:"argument's type argument" ~agree:( = ) env j
                     occ)
              with
              | Some (Cpp_ir.Type.Entity_application (g', [x], _)) when GlobRef.UserOrd.equal g g'
                && not (Cpp_ir.Types.prints_as_any x) ->
                Some x
              | _ -> None )
            | _ -> None )
          | None -> None )
        | _ -> None )
      (Param_pos.positioned fn_param_core_tys_orig)
  in
  (* The callee's leading phantoms, as its plan has them: it writes [void]
     at them when anything after them is written.  An erased argument there
     costs the call nothing. *)
  let phantom_vars =
    List.filter_map
      (fun p ->
        match (p.Callable_abi.write, p.Callable_abi.origin) with
        | Callable_abi.Phantom _, Callable_abi.From_scheme v -> Some v
        | _ -> None )
      (Callable_abi.template_head (callee_abi ~instances:0 id))
  in
  (* Each value is kept with the scheme variable it stands for, from here to
     the plan: a recovery that fills or drops one leaves the others where
     they are. *)
  let constant_at_higher_kind =
    let hk =
      Option.cata (fun t -> Type_util.higher_kinded_core_tvars [t]) IntSet.empty
        (find_type_opt id)
    in
    fun i ty ->
      IntSet.mem i hk
      && (not (Core_util.is_erased_type (resolve_meta ty)))
      && (not (core_type_contains_erased ty))
      && Core_util.eq_core_type (Core_util.apply_core_type ty [Core.Type.Unknown]) ty
  in
  (* The variables a call writes: those the callee's plan declares a
     parameter for.  A higher-kinded class parameter is none of them (it is
     the instance's associated type), nor is a result family the head leaves
     to deduction ([case_sum1]'s). *)
  let in_head =
    List.filter_map
      (fun p ->
        match p.Callable_abi.origin with
        | Callable_abi.From_scheme v -> Some v
        | _ -> None )
      (Callable_abi.template_head (callee_abi ~instances:0 id))
  in
  let mem v vs = List.exists (Scheme.Var.equal v) vs in
  let regular_of ?(keep = fun v -> mem v in_head) tys =
    Core_util.Var_types.bindings tys
    |> List.filter (fun (v, _) -> keep v)
    |> List.map
         (fun (v, ty) ->
           (* How the callee's type spells the variable, which the sets read
              off that type are keyed by. *)
           let i = Scheme.Var.ordinal v in
           (* A constant type function written at a higher-kinded variable is
              the constant carrier, not the head of the type it returns. *)
           let t =
             if constant_at_higher_kind i ty then carrier_template env tvars ty
             else Translation_types.template_arg_of_core_type ~site:Cpp_ir.Types.Through_tvar env tvars ty
           in
           (* A higher-kinded variable of the caller's reaching such a
              position is spelled as the template it is, which names no
              type; the position takes it at the erased element. *)
           let t =
             match (t, resolve_meta ty) with
             | (Member _ | Variable _), Core.Type.Variable {variable = j; _}
               when IntSet.mem i plain_carriers && caller_higher_kinded j ->
               Translation_types.template_arg_of_core_type ~site:Cpp_ir.Types.Through_tvar env tvars
                 (Core.Type.Variable_app {head = j; arguments = [Core.Type.Unknown]})
             | _ when (Cpp_ir.Types.prints_as_any t || Translation_tvars.under_applied_ind t)
                      && IntSet.mem i plain_carriers -> (
               match carrier_from_dictionary i with
               | Some t' -> t'
               | None -> t )
             | _ -> t
           in
           (* A variable this scope does not name is erased where it sits,
              as a binder spells it -- [std::pair<T2, Sum<std::any,
              std::any>>] for [bind]'s [S * (I + R)] with the method's own
              [I] and [R] gone.  Only a type that is nothing else says
              nothing. *)
           ( v,
             match t with
             | Variable (Index (_, None)) -> (Erased Type : Cpp_ir.Lowered.Type.t)
             | t when has_unnamed_tvar t -> Type_util.resolve_tvars_to_any t
             | t -> t ) )
    |> List.filter (fun (v, t) -> not (mem v phantom_vars && Cpp_ir.Types.prints_as_any t))
  in
  let regular_type_args = regular_of tys in
  (* Recover erased type args that C++ cannot deduce. Two cases: (a) tys is
     non-empty but all entries were erased (Core.Type.Erased Core.Erasure_reason.Type_argument) →
     filter_erased_type_args drops them all. (b) tys is empty — the Rocq
     extraction didn't supply type args at the call site, but the callee has
     Core.Type.Erased Core.Erasure_reason.Type_argument domain entries (erased type params).

     In both cases, if the callee's Core return type is a Core.Type.Variable that refers to
     one of those erased type params, and we know the concrete return type
     from the enclosing function context (current_cpp_return_type), we can
     supply it as an explicit C++ template arg.

     This is needed because C++ cannot deduce template type params from lambda
     arguments — lambdas don't participate in template argument deduction. *)
  let regular_type_args =
    let filtered =
      filter_erased_keyed
        ~preserve_positions:(Table.is_inline_custom id)
        regular_type_args
    in
    (* Whether the callee returns a variable of an erased type binder, and
       if so the variable and the concrete C++ type to use for it. *)
    let try_recover_erased_return_type () =
      match current_cpp_return_type () with
      | None -> None
      | Some ret_ty -> (
        match Option.map (fun t -> resolve_meta (core_return_type t)) (find_type_opt id) with
        | Some (Core.Type.Variable {variable = i; _}) -> (
          match scheme_var i with
          | Some v when erased_type_binder v -> Some (v, ret_ty)
          | _ -> None )
        | _ -> None )
    in
    (* Value args normally let C++ deduce the type params, but not when
       the return type variable occurs in no value parameter — as for a
       method of a higher-kinded class ([cout : forall A, F A -> A], whose
       only parameter is the instance's associated carrier type, a
       non-deduced context). *)
    let tvars_of = spelled_tvars_of in
    let deducible_tvars () = deducible_tvars_of_glob id in
    let ret_tvar_undeducible () =
      match (find_type_opt id, deducible_tvars ()) with
      | Some core_ty_orig, Some deducible -> (
        match resolve_meta (core_return_type core_ty_orig) with
        | Core.Type.Variable {variable = i; _} -> not (IntSet.mem i deducible)
        | _ -> false )
      | _ -> false
    in
    (* Whether any type variable of the callee at all is beyond deduction.
       Dropping the whole argument list rests on the compiler recovering it
       from the values; a variable no parameter spells is one it cannot, and
       then the list has to be written -- erased positions included, as
       [std::any], which is what they are. *)
    let some_tvar_undeducible () =
      match (find_type_opt id, deducible_tvars ()) with
      | Some core_ty_orig, Some deducible ->
        let all =
          List.fold_left tvars_of IntSet.empty
            (resolve_meta (core_return_type core_ty_orig)
             :: List.map resolve_meta (core_domains core_ty_orig))
        in
        not (IntSet.subset all deducible)
      | _ -> false
    in
    (* A higher-kinded argument is a type constructor, and [std::any] is not
       a spelling of one: a call reading one erased cannot be written out at
       all, so it keeps deducing -- whether or not its head declares a
       parameter there, as it does not for a result family it leaves to
       deduction.  Higher-kinded as the declaration has it
       ({!Type_util.higher_kinded_core_tvars}), not merely applied: an event
       family is applied everywhere it occurs and is still declared a plain
       [typename]. *)
    let no_erased_hkt_arg () =
      match find_type_opt id with
      | None -> true
      | Some core_ty ->
        let hk = declared_higher_kinded_tvars core_ty in
        not
          (List.exists
             (fun (v, t) -> IntSet.mem (Scheme.Var.ordinal v) hk && Cpp_ir.Types.prints_as_any t)
             (regular_of ~keep:(Callable_abi.keeps (callee_abi ~instances:0 id)) tys) )
    in
    (* Writing the list out is what this call is left with once the
       recoveries have declined, so an erased family is worth resolving from
       the value arguments first ({!resolve_from_argument_heads}): written as
       [std::any], it types whatever parameter the callee declares at it. *)
    (* A position still erased after that may be stated by the type the
       call is expected to produce: [trigger]'s event family, erased as a
       type-level function, is the family of the tree it is assigned to.
       The callee's declared codomain is matched against it. *)
    let from_expected targs =
      let names, m = Lazy.force result_tvar_map in
      (* A type-level lambda extraction could only write as its head
         ({!Translation_tvars.under_applied_ind}) is filled the same way. *)
      List.map
        (fun (v, t) ->
          let i = Scheme.Var.ordinal v in
          let bound () =
            match
              Option.bind
                (if i >= 1 then List.nth_opt names (i - 1) else None)
                (fun name -> List.find_opt (fun (v, _) -> Id.equal v name) m)
            with
            | Some (v, t') -> (
              match erase_carrier_elements i t' with
              | Some t'' -> Some (v, t'')
              | None -> None )
            | None -> None
          in
          ( v,
            if Cpp_ir.Types.prints_as_any t || Translation_tvars.under_applied_ind t then
              match bound () with
              | Some (_, t') -> t'
              | None -> t
            (* Erased only in part -- a carrier [fun T => option (exp T)]
               written [std::optional<std::any>] -- the result fills the
               part it knows. *)
            else if Type_util.has_tany_written t then
              match bound () with
              | Some (_, t') -> Type_util.refine_erased_by ~expected:t' t
              | None -> t
            else t ) )
        targs
    in
    let written_out () =
      if some_tvar_undeducible () && no_erased_hkt_arg () then
        filter_erased_keyed ~preserve_positions:true
          (from_expected
             (regular_of
                (Call_tyargs.by_variable (resolve_from_argument_heads ~lex tyargs primary_core_args)) ) )
      else filtered
    in
    if filtered = [] && regular_type_args <> [] && dictionary_filled then
      filter_erased_keyed ~preserve_positions:true regular_type_args
    else if filtered = [] && regular_type_args <> [] then
      (* Case (a): tys was non-empty but all got filtered. Only attempt
         recovery when there are no non-erased value args — if there are value
         args, C++ can deduce the template types from them (and injecting
         explicit type args may conflict with the template signature, e.g.
         hk_map's F0/F1 are function types). *)
        match
          if args = [] || ret_tvar_undeducible () then
            try_recover_erased_return_type ()
          else None
        with
      | Some (v, ret_ty) ->
        (* The erased variable is the concrete return type; any other erased
           entry is dropped. *)
        List.map
          (fun (w, t) -> (w, if Scheme.Var.equal w v then ret_ty else t))
          regular_type_args
        |> List.filter (fun (_, t) -> not (Cpp_ir.Types.prints_as_any t))
      | None -> written_out ()
    else if Core_util.Var_types.is_empty tys then
      (* Case (b): tys is empty — synthesize type args from scratch. Build one
         entry per Core.Type.Erased Core.Erasure_reason.Type_argument domain position.

         Recovery is attempted when:
         - [args = []] — no value args, so C++ can't deduce types.
         - [concrete_tvar_type <> None] — the callee's return type [Core.Type.Variable]
           was resolved from excess args + enclosing return type. *)
      let should_recover =
        args = [] || concrete_tvar_type <> None || ret_tvar_undeducible ()
      in

        match
          if should_recover then try_recover_erased_return_type () else None
        with
      | Some (_, ret_ty) ->
        (* Use [concrete_tvar_type] when available (excess args case),
           otherwise fall back to the enclosing function's return type, at
           every variable of an erased type binder. *)
        let t1 = Option.default ret_ty concrete_tvar_type in
        List.map
          (fun v -> (v, t1))
          (List.filter erased_type_binder (Option.cata Core.Schema.vars [] schema))
      | None -> filtered
    else
      from_expected filtered
  in
  regular_type_args
  in
  let instance_args = List.filter_map Fun.id typeclass_type_args in
  let abi = callee_abi ~instances:(List.length instance_args) id in
  (* A plain position takes a type: a family recovered as its bare head --
     [box] for [TFunctor_list'], whose [F] the declaration writes plain -- is
     that family at its erased index. *)
  let at_plain_positions regular =
    let hk =
      Option.cata (fun t -> Type_util.higher_kinded_core_tvars [t]) IntSet.empty
        (find_type_opt id)
    in
    List.map
      (fun (v, t) ->
        ( v,
          if (not (IntSet.mem (Scheme.Var.ordinal v) hk)) && Translation_tvars.under_applied_ind t then
            Translation_tvars.saturate_at_any t
          else t ) )
      regular
  in
  let apply regular =
    let regular = at_plain_positions regular in
    Template_application.plan abi
      ~instance:(fun k -> List.nth_opt instance_args k)
      ~scheme:(fun v -> Scheme.Var.assoc_opt v regular)
  in
  let regular = build_type_args tyargs in
  (* A class parameter is quantified first, so the carrier is the callee's
     first variable. *)
  let carrier_first carrier = Option.cata (fun v -> [(v, carrier)]) [] (scheme_var 1) in

  (* Nothing survived the erasure filters, so if the callee opens with
     parameters its signature never mentions, deduction has nothing to work
     from and the call has to name them. *)
  let regular =
    if regular = [] && instance_args = [] then
      (* The call writes nothing, so every parameter is left to deduction --
         and a type constructor is the one thing deduction can get wrong
         rather than merely miss.  Where it cannot be read off the value
         argument, name it -- the carrier is the callee's first variable. *)
      match
        hkt_carrier_type_args env tvars ?result:expected_ty id tys
      with
      | Some [carrier] -> carrier_first carrier
      | _ -> (
        (* The result did not say what the carrier is; the dictionary the
           call passes for the class still does. *)
        match dict_carrier_type_args env tvars id primary_core_args with
        | Some [carrier] -> carrier_first carrier
        | _ ->
          (* Neither route knew the carrier.  An argument's type may still
             say what an erased plain type argument was, which is worth
             writing only here: filling a position is what would have taken
             the two routes above out of reach. *)
          build_type_args (resolve_from_argument_heads ~lex tyargs primary_core_args) )
    else
      (* A list the call does write may still hold a family Core erased
         -- [translate inr1]'s source, taken off a morphism that erases it --
         which the argument constrained in it names.  Written erased, the
         argument is read at the erased family: converted node by node. *)
      (* Not where the family is an axiom: it has no struct to name. *)
      let no_struct f =
        match resolve_meta f with
        | Core.Type.Global_app {head = g; _} ->
          Table.is_custom g
          || (match g with
              | GlobRef.IndRef _ -> false
              | GlobRef.ConstRef kn -> not (Option.has_some (Table.lookup_typedef_unchecked kn))
              | _ -> true)
        | _ -> false
      in
      let refined =
        resolve_from_argument_heads ~accept:(fun _ f -> not (no_struct f)) ~lex tyargs
          primary_core_args
      in
      if List.equal Scheme.Var.equal (Call_tyargs.holes refined) (Call_tyargs.holes tyargs)
      then regular
      else
        match build_type_args refined with
        | [] when instance_args = [] -> regular
        | refilled -> refilled
  in
  let application = apply regular in
  let all_type_args = Template_application.to_list application in

  (* An argument written as an erased placeholder at a variable the use
     wrote nothing for, and nothing resolved since, is a guess: such a
     variable is C++'s to deduce. *)
  let guessed =
    List.concat
      (List.mapi
         (fun k p ->
           match (p.Callable_abi.origin, List.nth_opt all_type_args k) with
           | Callable_abi.From_scheme v, Some a
             when Cpp_ir.Types.prints_as_any a && Call_tyargs.is_unwritten tyargs v ->
             [ Printf.sprintf "variable %d, of which nothing is known, is written as %s"
                 (Scheme.Var.ordinal v)
                 (Pp.string_of_ppcmds (Cpp_print.pp_cpp_type false [] a)) ]
           | _ -> [] )
         (Callable_abi.template_head abi) )
  in
  List.iter
    (fun problem ->
      Probe.violation "template application"
        Pp.(str "the call to " ++ GlobRef.print id ++ str ": " ++ str problem) )
    (Template_application.validate abi application @ guessed);
  (* The written arguments that instantiate the callee's own type variables,
     by variable: each argument the plan wrote at a parameter declaring one,
     and at a carrier the call's class resolves -- a variable the head does
     not keep, quantified first ([MonadIter_stateT0]'s [M]) -- the
     dictionary written for it. *)
  let written_tvar_args =
    let by_parameter =
      List.concat
        (List.mapi
           (fun k p ->
             match (p.Callable_abi.origin, List.nth_opt all_type_args k) with
             | Callable_abi.From_scheme v, Some t -> [(v, t)]
             | _ -> [] )
           (Callable_abi.template_head abi) )
    in
    let carriers = Callable_abi.dictionary_carriers abi in
    let dictionaries =
      List.filteri
        (fun j _ -> j >= List.length instance_args - List.length carriers)
        instance_args
    in
    List.combine
      (List.filteri (fun j _ -> j < List.length dictionaries) carriers)
      (List.filteri (fun j _ -> j < List.length carriers) dictionaries)
    @ by_parameter
  in
  {
    callee = id;
    plan = plan;
    callee_type = ty;
    written = tys;
    abi = abi;
    application = application;
    written_by_var = written_tvar_args;
  }

(** The callee [id]'s type variables as the type [expected] that its result
    lands in instantiates them: its declared codomain, with the variables
    named [_R1].. (apart from the caller's own), matched against [expected].
    Returns the names and the bindings found.  [explicit] says [expected] is
    the call's own slot rather than the enclosing function's result, which is
    evidence for a bare-variable codomain only in the first case.  Where
    [expected] is a callable and the codomain is not, the call is the callable
    -- an instance function passed as a dictionary -- and the callable's
    result is what the codomain meets. *)
let callee_result_bindings env id ~explicit (expected : Cpp_ir.Lowered.Type.t option) =
  match (expected, callee_core_type id) with
  | Some exp, Some core_ty ->
    let n = IntSet.fold max (collect_tvars_set IntSet.empty core_ty) 0 in
    let names =
      List.init n (fun i -> Generated_name.indexed "R" (i + 1))
    in
    let cod : Cpp_ir.Lowered.Type.t =
      match Translation_types.cpp_ir_of_core_type env names (type_simpl core_ty) with
      | Function (_, c) -> c
      | t -> t
    in
    (* A family is written applied at an erased index and declared plain: in
       the pattern it is the variable itself. *)
    let cod = Translation_tvars.deapply_family_variables cod in
    (* The enclosing function's result is this call's only where the call is
       what it returns, which nothing here says; a codomain with structure has
       to match it to count as evidence, a bare variable matches anything --
       [tfmap f (ops b)] inside [TFunctor_bundle] read [bundle<std::any>] for
       the list. *)
    let bare_cod = match cod with Variable _ -> true | _ -> false in
    let rec strip_param_spelling : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
      | Non_deduced t | Const t | Reference (_, t) -> strip_param_spelling t
      | t -> t
    in
    let exp =
      let as_fun t = Translation_types.unfold_cpp_typedef env (strip_param_spelling t) in
      match (as_fun exp, cod) with
      | Function (_, c), (Entity_application _ | In_namespace _) -> c
      | e, _ -> e
    in
    if (not explicit) && bare_cod then (names, [])
    else
      ( names,
        List.filter
          (fun (_, t) -> not (Cpp_ir.Types.prints_as_any t))
          (Type_util.extract_tvar_map cod (Translation_types.unfold_cpp_typedef env exp)) )
  | _ -> ([], [])

(** An instance's type argument extraction could not express -- a family
    that is a type-level lambda, [AllE := fun X => aE X + bE X] -- is erased
    from [ts], the instance's arguments.  A call's result says what it was:
    the instance's carrier ([box E] for [Monad_box]) heads the type the method
    returns, and its arguments are matched against the [expected] one's.
    [ts] instantiates the instance's variables in order, so position [k] is
    [Core.Type.Variable (k + 1)], named [names.(k)] in the carrier pattern returned.  [None]
    where nothing is erased or nothing matches. *)
let instance_family_binding env r ts (expected : Cpp_ir.Lowered.Type.t option) =
  let erased t = Core_util.is_erased_type (resolve_meta t) in
  match (expected, find_type_opt r) with
  | Some exp, Some inst_ty
    when List.exists (fun (_, t) -> erased t) (Core_util.Var_types.bindings ts) -> (
    (* Counted with application heads: a family may occur only applied
       ([itree (E _) R]). *)
    let names =
      List.init (IntSet.fold max (collect_tvars_set IntSet.empty inst_ty) 0) (fun i ->
          Generated_name.indexed "I" (i + 1) )
    in
    (* An instance of a definitional class is the function the class
       abbreviates -- [MonadIter_itree : forall E R I, (I -> itree E (I + R))
       -> I -> itree E R] -- and its result is what the carrier heads. *)
    match
      match resolve_meta (core_codomain inst_ty) with
      | Core.Type.Global_app {head = c; type_arguments = carrier :: _; _} when Table.is_typeclass c -> Some carrier
      | Core.Type.Global_app _ as cod -> Some cod
      | _ -> None
    with
    | Some carrier -> (
      (* A family is written applied until it is deapplied: in the pattern
         it is the variable itself. *)
      let carrier =
        Type_util.unqualify_ty
          (Translation_tvars.deapply_family_variables (Translation_types.cpp_ir_of_core_type env names carrier))
      in
      match (carrier, Type_util.unqualify_ty (Translation_types.unfold_cpp_typedef env exp)) with
      | Entity_application (h1, cargs, _), Entity_application (h2, eargs, _)
        when GlobRef.CanOrd.equal h1 h2 && List.length cargs <= List.length eargs ->
        let m =
          List.filter
            (fun (_, t) -> not (Cpp_ir.Types.prints_as_any t))
            (List.concat
               (List.map2 Type_util.extract_tvar_map cargs
                  (safe_firstn (List.length cargs) eargs) ) )
        in
        if m = [] then None else Some (carrier, names, m)
      | _ -> None )
    | _ -> None )
  | _ -> None

let rec core_arg_to_template_type ?expected env core_arg : Cpp_ir.Lowered.Type.t option =
  (* [None] for skipped infrastructure (ReSum instances, say): it is passed
     as a dictionary, so it is told apart from the regular arguments, but it
     has no struct and so no type to write.

     The type arguments an instance's generated struct has parameters for.

     Its declaration mints one per parameter erasure left standing, so a type
     argument erasure removed has no position to be written at and an argument
     written for it overruns the template head -- [ParamsV<IPZ, std::any>]
     against [template <IPtr _tcI0> struct ParamsV].  Erased instance
     parameters are already gone from the application's arguments by the time
     this sees them; an erased {e type} parameter is still in the [Core.Expr.Global]'s
     list, as [Core.Type.Erased], and this is where it leaves.

     {!Type_util.filter_erased_type_args} is the same all-or-nothing filter
     a call applies to its own: a position is what gives the others their
     meaning, so one that cannot be written costs the list. *)
  (* The variables the instance's struct declares a template parameter for,
     in its head's order ({!Instance_methods.instance_tvars}), among those
     the use writes an argument for. *)
  let struct_vars r ts =
    let ty = find_type r in
    List.filter
      (fun j -> Core_util.Var_types.find_tvar ts j <> None)
      (Instance_methods.instance_tvars ty (Instance_methods.class_type ty))
  in
  let instance_type_args r ts =
    Type_util.filter_erased_type_args
      (Translation_types.build_template_params ~site:Cpp_ir.Types.Through_tvar env []
         (List.filter_map (Core_util.Var_types.find_tvar ts) (struct_vars r ts)) )
  in
  let instance_type_args_from_expected r ts =
    match instance_family_binding env r ts expected with
    | None -> None
    | Some (_, names, m) ->
      (* Variable [j] is the instance's [j]th family name. *)
      let filled =
        List.map
          (fun (v, t) ->
            let j = Scheme.Var.ordinal v in
            ( j,
              if not (Core_util.is_erased_type (resolve_meta t)) then
                Some (List.hd (Translation_types.build_template_params ~site:Cpp_ir.Types.Through_tvar env [] [t]))
              else
                Option.bind (List.nth_opt names (j - 1)) (fun v ->
                    Option.map snd (List.find_opt (fun (v', _) -> Id.equal v v') m) ) ) )
          (Core_util.Var_types.bindings ts)
      in
      if List.for_all (fun (_, o) -> o <> None) filled then
        Some
          (List.filter_map
             (fun j -> match List.assoc_opt j filled with Some o -> o | None -> None)
             (struct_vars r ts) )
      else None
  in
  match strip_dictionary core_arg with
  | Core.Expr.Global ({callee = r; _} as use) ->
    let ts = Core_util.written_type_args use in
    if ref_returns_skipped r then None
    else
      (* Use the instance struct as a type - convert to Core.Type.Global_app *)
      Some
        (Cpp_ir.Type.Entity_application
           ( r,
             ( match instance_type_args_from_expected r ts with
             | Some args -> args
             | None -> instance_type_args r ts ),
             [] ))
  | Core.Expr.Bound_variable {index = i; _} ->
    (* The instance is a lambda parameter - look up its name in the env and
       create a Core.Type.Variable reference to the template parameter *)
    let db, _ = env in
    let name = List.nth db (pred i) in
    Some (Cpp_ir.Type.Variable (Named name))
  | Core.Expr.Apply {callee = Core.Expr.Global {callee = r; _}; _} when ref_returns_skipped r -> None
  | Core.Expr.Apply {callee = Core.Expr.Global ({callee = r; _} as use); arguments = inner_args} ->
    let ts = Core_util.written_type_args use in
    (* Parameterized instance application, e.g. numList A H. Convert to
       Core.Type.Global_app(r, template_args, []) where template_args are built from the
       inner args. *)
    let template_args =
      List.filter_map
        (fun arg ->
          match arg with
          | Core.Expr.Erased_value _ -> None (* Erased type param — skip *)
          | _ -> core_arg_to_template_type env arg )
        inner_args
    in
    (* Instance parameters come first in the generated struct's template
       list ([template <typename _tcI0, typename T1>]), so the instance
       arguments must precede the type arguments here too. *)
    Some (Cpp_ir.Type.Entity_application (r, template_args @ instance_type_args r ts, []))
  | Core.Expr.Match {scrutinee; branches; _}
    when Array.length branches = 1 ->
    (* Record field projection — e.g., [base_category(PS)].
       Resolve to [Tqualified(scrutinee_type, field_name)]. *)
    let {Core.Match.Branch.binders = binds; body = br_body; _} = branches.(0) in
    Option.map
      (fun base_ty ->
        match br_body with
        | Core.Expr.Bound_variable {index = j; _} when j >= 1 && j <= List.length binds -> (
          let idx = List.length binds - j in
          let field_id, _ = List.nth binds idx in
          match field_id with
          | Core.Binder_name.Source name | Core.Binder_name.Generated name -> Cpp_ir.Type.Member (base_ty, name)
          | Core.Binder_name.Anonymous -> Cpp_ir.Type.Any )
        | _ -> Cpp_ir.Type.Any )
      (core_arg_to_template_type env scrutinee)
  | Core.Expr.Apply {callee = f; arguments = args} ->
    (* Parameterized instance application with non-glob head.
       Resolve head, then add arg types. *)
    let arg_tys =
      List.filter_map
        (fun arg ->
          match arg with
          | Core.Expr.Erased_value _ -> None
          | _ -> ( try core_arg_to_template_type env arg with _ -> None ) )
        args
    in
    Option.map
      (fun (t : Cpp_ir.Lowered.Type.t) ->
        match t with
        | Entity_application (r, existing, es) -> Cpp_ir.Type.Entity_application (r, existing @ arg_tys, es)
        | head_ty -> head_ty )
      (core_arg_to_template_type env f)
  | Core.Expr.Erased_value _ -> Some Cpp_ir.Type.Any (* Should not happen at top level, but be safe *)
  | _ ->
    CErrors.anomaly
      (Pp.str
         "core_arg_to_template_type: unexpected ML term after \
          is_typeclass_instance_arg filter" )

(** Whether the global [id] takes the callable it declares at [pos] as a
    deduced [F &&]: the callee then calls it at its own instantiation, and an
    argument written against the erased slot -- adapted to unbox
    [List<std::any>] where the callee hands it a [List<T2>] -- reads the
    wrong type out of every box ({!Callable_abi.deduces_callable}). *)
let deduces_callable = Callable_abi.deduces_callable

(** For the function [r] of the unit, [b] its body and [ty] its type, the
    declared positions of the callables a call to it assumes it deduces where
    no plan of it is recorded -- a custom mapping's, a projection's: those
    its signature would generalise were it generated as a function
    ({!Translation_callable_params.generalises_callable}), its body read for the ones it holds on to. *)
let assumed_deduced_callables r b ty =
  let ids, _ = collect_typed_lams ty b in
  let binder_tys = List.rev_map snd ids in
  let ungeneralised = Translation_callable_params.ungeneralised_callables_of_definition r ty b in
  let declared t = Translation_types.cpp_ir_of_core_type (Common.empty_env ()) [] (type_simpl t) in
  match find_type_opt r with
  | None -> []
  | Some fn_core_ty -> (
    match declared fn_core_ty with
    | Function (dom, cod) ->
      let primary = primary_tvar_indices dom cod in
      List.filter_map
        (fun (pos, pt) ->
          match (declared pt, Param_pos.source_index binder_tys pos) with
          | (Function _ as f), Some i
            when Translation_callable_params.generalises_callable ~kept_as_fn:(Escape.IntSet.mem i ungeneralised)
                   ~primary f ->
            Some pos
          | _ -> None )
        (Param_pos.positioned (Param_pos.orig_params ~expand:expand_core_fun_alias fn_core_ty))
    | _ -> [] )

(** {!assumed_deduced_callables} for each function of [struc] that none of
    the plans [callables] is of. *)
let assumed_callables struc callables =
  let planned =
    List.fold_left
      (fun s abi -> GlobRef.Map_env.add (Callable_abi.callee abi) () s)
      GlobRef.Map_env.empty callables
  in
  List.filter_map
    (fun (r, b, ty) ->
      if GlobRef.Map_env.mem r planned then None
      else Some (r, assumed_deduced_callables r b ty) )
    (Modutil.struct_functions struc)

(** [slot] for a lambda going to a callable its callee deduces: the positions
    the slot erases are left to deduction ([const auto&]), so the lambda takes
    whatever its callee's instantiation hands it there. *)
let deduce_erased_domains : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Function (doms, cod) ->
    Function
      ( List.map
          (fun d ->
            if Cpp_ir.Types.exists Cpp_ir.Types.prints_as_any d then Cpp_ir.Type.Reference (Lvalue, Const Auto) else d )
          doms,
        cod )
  | t -> t

(** [record_call_sig env callee_ty e] records what the callee's Core type says
    about [e], when [e] is a call nothing has been recorded on yet.

    The application site is where the answer is known; the call node
    is built further down, in {!eta_fun}, so the answer is stamped on here
    rather than threaded through every intermediate that only forwards it.  A
    callee with no Core type, or one that is not a call at all, keeps
    its untyped signature: a consumer must defer to C++ deduction rather than invent
    a type.

    Both fields come off the {e same} instantiated type, so a consumer reading
    one cannot be looking at a different callee than a consumer reading the
    other.  The parameter list is kept only when it has one entry per
    argument -- {!Cpp_ir.Build.signature} enforces that -- since a partial
    application, or a callee whose arrows an eta-expansion has rearranged,
    would otherwise hand the printer a misaligned list. *)
let record_call_sig env callee_ty (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match (e, callee_ty) with
  | Call ({yields = Untyped; params = Unknown; _}, f, args), Some core_ty ->
    let cpp_of ml = Translation_types.cpp_ir_of_core_type env [] ml in
    ( match cpp_of (core_codomain core_ty) with
    | exception e' when CErrors.noncritical e' -> e
    | ty ->
      let params =
        try Some (List.map cpp_of (core_value_domains core_ty))
        with e' when CErrors.noncritical e' -> None
      in
      let sg = Cpp_ir.Build.signature ~yields:ty ?params ~nargs:(List.length args) () in
      (* An over-application is a call of the call that took the callee's
         own arguments, and that one yields the callable the rest are applied
         to: what is left of the type once its arguments are taken. *)
      let f : Cpp_ir.Lowered.Expr.t =
        match f with
        | Call ({yields = Untyped; params = Unknown; _}, g, inner_args) -> (
          match cpp_of (Type_util.core_drop_arrows (List.length inner_args) core_ty) with
          | exception e' when CErrors.noncritical e' -> f
          | Any | Obligation Opaque_type -> f
          | inner_ty ->
            Call (Cpp_ir.Build.signature ~yields:inner_ty ~nargs:(List.length inner_args) (), g, inner_args) )
        | f -> f
      in
      Call (sg, f, args) )
  | _ -> e

(* The callees whose result bindings are being computed.  Reading the
   expected type can convert value arguments that a type carries, and
   generating one of them can be the very call whose binding is asked for: a
   binding cannot depend on itself, so the inner request finds none. *)
let binding_results = ref Names.GlobRef.Set_env.empty

let binding_results_of id compute =
  if Names.GlobRef.Set_env.mem id !binding_results then ([], [])
  else begin
    binding_results := Names.GlobRef.Set_env.add id !binding_results;
    Fun.protect
      ~finally:(fun () -> binding_results := Names.GlobRef.Set_env.remove id !binding_results)
      compute
  end

(** [plan_call ?expected_ty env inst] -- what the instantiated call [inst]
    ({!Core_elaborate.instantiate}) needs to know before its arguments are
    generated, beyond its instantiation: the C++ types its result and its
    dictionaries are expected at, and what those say of the callee's
    variables.  Read by {!gen_call_args} and by the assembly in {!eta_fun}.
    Nothing here changes the instantiation. *)
let plan_call ~lex ?(expected_ty : Cpp_ir.Lowered.Type.t option) env (inst : Elaborated_call.instantiated) =
  let {
    Elaborated_call.call =
      {
        Elaborated_call.callee = id;
        primary = primary_core_args;
        excess = excess_args;
        instances = typeclass_core_args;
        _
      };
    tys;
    _
  } =
    inst
  in
  let expected_result = expected_ty in
  (* Where the position erased the result's family, the arguments may still
     state it: [interp intr prog] as the source of an [interp_state] is
     expected at [Itree<std::any, Nat>], and [intr : TopE ~> itree TopE]
     says the monad is [itree TopE].  The instances' families are read off
     this. *)
  let expected_result =
    let from_args () =
      match
        tvar_instantiation_found ~lex ~constructors:true
          (find_type id) primary_core_args
      with
      | [] -> None
      | found ->
        (* A carrier bound as a head partially applied ([itree TopE]) is
           applied by appending: the hole inside its family is the family's
           own erased index, not the argument the carrier is missing. *)
        let rec subst t =
          match resolve_meta t with
          | Core.Type.Variable {variable = i; _} -> (
            match List.assoc_opt i found with Some b -> b | None -> t )
          | Core.Type.Variable_app {head = k; arguments = args} -> (
            let args = List.map subst args in
            match List.assoc_opt k found with
            | Some (Core.Type.Global_app {head = g; type_arguments = fixed; index_arguments = l}) ->
              Core.Type.Global_app {head = g; type_arguments = fixed @ args; index_arguments = l}
            | Some b -> Core_util.apply_core_type b args
            | None -> Core.Type.Variable_app {head = k; arguments = args} )
          | Core.Type.Global_app {head = g; type_arguments = args; index_arguments = l} ->
            Core.Type.Global_app {head = g; type_arguments = List.map subst args; index_arguments = l}
          | Core.Type.Arrow {parameter = a; result = b} -> Core.Type.Arrow {parameter = subst a; result = subst b}
          | t -> t
        in
        let t = Translation_types.cpp_of_core env (subst (core_codomain (callee_core_type_exn id))) in
        Translation_types.spell_in_scope t
    in
    match expected_result with
    | Some e when Cpp_ir.Types.exists Cpp_ir.Types.prints_as_any e -> (
      match from_args () with
      | Some a -> Some (Type_util.refine_erased_by ~expected:a e)
      | None -> expected_result )
    (* With no expected type of its own the call may not be the enclosing
       function's result at all -- a let-bound computation over another
       family -- so what its arguments state comes before that result. *)
    | None -> (
      match from_args () with
      | Some _ as a -> a
      | None -> current_cpp_return_type () )
    | _ -> expected_result
  in
  let typeclass_type_args =
    List.map
      (core_arg_to_template_type ?expected:expected_result env)
      typeclass_core_args
  in
  (* The families the call's instances were found to have: the slots their
     arguments are generated against erase them the same way. *)
  let instance_families =
    List.filter_map
      (fun a ->
        match strip_magic a with
        | Core.Expr.Global ({callee = r; _} as use) ->
          instance_family_binding env r (Core_util.written_type_args use)
            expected_result
        | _ -> None )
      typeclass_core_args
  in
  (* {b Concrete T1 for excess-arg calls.}  When [tys = []] and there
     are excess args, the callee's polymorphic return type [Core.Type.Variable i] can't
     be resolved by substitution.  We compute the concrete type [T1]
     from the enclosing function's return type and the excess args' types:
     [T1 = excess_arg_types -> enclosing_return_type].

     This value is used in two places:
     1. Lambda arity limiting: to annotate the split outer lambda's
        return type (needed for [is_invocable_r_v] concept checking).
     2. Template arg recovery: as an explicit template argument at the
        call site (C++ can't deduce [T1] from lambda args). *)
  let tvars = get_current_type_vars () in
  let concrete_tvar_type =
    if (not (Core_util.Var_types.is_empty tys)) || excess_args = [] then
      None
    else
      match current_cpp_return_type () with
      | None -> None
      | Some ret_ty ->
        match find_type_opt id with
        | None -> None
        | Some core_ty_orig ->
          let ret = Type_util.resolve_meta (core_return_type core_ty_orig) in
          ( match ret with
          | Core.Type.Variable _ ->
            (* The excess arguments' C++ types, where each is a parameter. *)
            let excess_cpp_tys =
              List.filter_map
                (fun core_arg ->
                  match core_arg with
                  | Core.Expr.Bound_variable {index = i; _} ->
                    Option.map (Translation_types.cpp_ir_of_core_type env tvars) (parameter_type env i)
                  | _ -> None )
                excess_args
            in
            if List.length excess_cpp_tys = List.length excess_args then
              Some (Cpp_ir.Type.Function (excess_cpp_tys, ret_ty))
            else
              None
          | _ -> None )
  in
  (* When the function is typeclass-parameterized and call-site args include
     concrete instances, compute a promoted-var→concrete-type map so that
     custom constructors (nil/cons) inside arg expressions use concrete
     element types instead of std::any.  E.g., [mfold nat_monoid [1;2;3]]
     resolves m_carrier → uint64_t for the list construction. *)
  let instance_promoted_map =
    List.concat_map (fun tc_arg ->
      match tc_arg with
      | Core.Expr.Global {callee = r; _} ->
        List.filter_map (fun (var_name, core_ty) ->
          let cpp_ty = Translation_types.cpp_of_core env core_ty in
          if Cpp_ir.Types.prints_as_any cpp_ty then None
          else Some (var_name, cpp_ty)
        ) (Table.get_instance_promoted_types r)
      | _ -> []
    ) typeclass_core_args
  in
  (* The callee's variables as the call's expected result instantiates
     them: its declared codomain, named [T1]..[Tn] and with a plain family's
     application taken off, matched against that type.  Read by the argument
     loop below for a parameter the substitution left erased. *)
  let result_tvar_map =
    lazy
      (binding_results_of id (fun () ->
           callee_result_bindings env id
             ~explicit:(expected_ty <> None)
             ( match expected_ty with
             | Some _ -> expected_ty
             | None -> current_cpp_return_type () ) ) )
  in
  {
    instantiated = inst;
    expected_result = expected_result;
    instance_type_args = typeclass_type_args;
    instance_families = instance_families;
    tvars = tvars;
    concrete_tvar_type = concrete_tvar_type;
    instance_promoted = instance_promoted_map;
    result_tvar_map = result_tvar_map
  }

(** Where the [i]th regular argument of a call is generated: the parameter
    it is passed at ([index] of the unsubstituted list, [param] its
    substituted Core type), the C++ type it is generated against
    ([expected]), and the return type in force while it is ([ret]),
    with what {!gen_call_args} reads of these afterwards. *)
type argument_position = {
  index : Param_pos.orig Param_pos.pos;
  param : Core.Type.t option;
  expected : Cpp_ir.Lowered.Type.t option;
  ret : Cpp_ir.Lowered.Type.t option;
  tvar_erased : bool;
  written_by_call : bool;
  deduced_callable : bool;
  expected_subst : Cpp_ir.Lowered.Type.t option;
}

(** Whether the variable [j], read at [occ], holds a function, by the C++
    type the representation plan gives its binder, failing one by its Core
    type; under [CRANE_CHECK_IR] held to the same reading of the type
    lowering recorded for the binder. *)
let local_callable env j occ =
  let callable ty =
    let ty = match ty with Some _ -> ty | None -> Option.map (Translation_types.cpp_of_core env) (get_env_type_opt j) in
    match Option.map (Translation_types.unfold_cpp_typedef env) ty with
    | Some (Cpp_ir.Type.(Function _ | Const (Function _) | Reference (_, (Function _ | Const (Function _))))) -> true
    | _ -> false
  in
  callable
    (Translation_binders.planned_binder_type ~use:"local callable" ~agree:(fun p l -> callable p = callable l) j occ)

(** [argument_position ~local_callable env id plan i core_arg] -- where the
    [i]th regular argument [core_arg] of the call to [id] planned as [plan]
    ({!plan_call}) is generated: {!argument_position}.  [local_callable j
    occ] says whether the variable [j] read at [occ] holds a function. *)
let argument_position ~local_callable env id plan i core_arg =
  let {
    instantiated =
      {
        Elaborated_call.call = {Elaborated_call.callee_type = fn_core_ty; _} as call;
        tys;
        params = fn_param_core_tys;
        params_orig = fn_param_core_tys_orig;
        subst_index_of_orig;
        _
      };
    instance_families = instance_families;
    result_tvar_map = result_tvar_map;
    _
  } = plan in
  let leading_params = Elaborated_call.leading_params call in
  let dictionary_filled = Elaborated_call.dictionary_filled call in
  (* The callee's parameters are indexed from its class-dictionary
     arguments, which [regular_core_args] does not include, so this
     argument's parameter is at [param_index] of the unsubstituted list --
     and, being a position of that list, has to be converted before it
     indexes the substituted one (see [subst_index_of_orig]). *)
  let param_index = Param_pos.of_regular ~leading:leading_params i in
  (* Where that parameter stands in the substituted list.  The
     conversion is a statement about the callee's Core type, and it is worth
     making only where the Core type is what the callee's C++ signature was
     built from.

     For a callee whose C++ form is written out by hand it is not: the
     replacement text is what says how the arguments are taken, and it
     need not take them at the Rocq types.  [crane_itree.h] invokes
     [itree_vis]'s continuation at [std::any] whatever its Rocq domain
     [X] is, so the substituted domain ([std::monostate]) is the one type
     the lambda will never be called at -- while [itree_bind]'s, two lines
     away in the same header, is taken at exactly its Rocq domain.
     Nothing here can tell those apart, so such a callee keeps reading the
     position it always read: no better answer is available, and a
     confident wrong one is worse than the familiar one. *)
  let subst_param_index =
    if Table.is_inline_custom id then
      Some (Param_pos.subst_at_declared param_index)
    else subst_index_of_orig param_index
  in
  (* Where substitution erased the parameter -- [IFun b c] at objects the
     call erases -- the declaration still takes it, at the type it
     declares, and an argument reaching it is recovered at that type. *)
  let param_core_ty =
    match subst_param_index with
    | Some i -> Param_pos.nth fn_param_core_tys i
    | None -> (
      match Param_pos.nth fn_param_core_tys_orig param_index with
      | Some t when not (erased_by_extraction t) -> Some t
      | _ -> None )
  in
  let param_expected_at params pos =
    match Param_pos.nth params pos with
    | Some core_ty ->
      let cpp_ty = Translation_types.cpp_of_core env core_ty in
      if Cpp_ir.Types.prints_as_any cpp_ty then None else Some cpp_ty
    | None -> None
  in
  (* The concrete types come from the substituted parameter type, but its
     {e arity} must come from the unsubstituted one: substituting a
     function type into a codomain that was a type variable flattens the
     element's arrows into the callable's own parameter list, and a
     template argument keeps its currying (see
     {!Translation_types.template_arg_of_core_type}).  A parameter declared as a bare type
     variable has arity zero, so its value is curried throughout. *)
  (* This parameter's substituted C++ type.  [param_index] counts
     positions of the unsubstituted type, so it has to be converted before
     it indexes the substituted list -- see [subst_index_of_orig]. *)
  let param_expected_subst () =
    Option.bind subst_param_index (param_expected_at fn_param_core_tys)
  in
  (* Just the re-currying: [None] where the declaration's arity is already
     the shape the substituted parameter type has, so a producer that has
     its own better source keeps it. *)
  let param_expected_recurried () =
    match Param_pos.nth fn_param_core_tys_orig param_index with
    | Some orig ->
      Option.bind (param_expected_subst ())
        (Cpp_ir.Types.respell_arrows (Cpp_ir.Types.Declared_at (count_core_value_arrows orig)))
    | None -> None
  in
  let param_expected_at_declared_arity () =
    match param_expected_recurried () with
    | Some _ as t -> t
    | None -> (
      match Param_pos.nth fn_param_core_tys_orig param_index with
      | Some _ -> param_expected_subst ()
      | None -> None )
  in
  (* The callee declares this parameter as one of its own template
     parameters [Core.Type.Variable j], and some {e other} parameter carries that same
     [j] in a position the instantiation erased -- so that parameter's
     argument deduces [j] as [std::any].  This one has to arrive boxed for
     the two deductions to agree.  Erasure of the type argument alone is
     not enough of a reason: unless another position states it as
     [std::any], boxing here would be the only thing making the deduction
     disagree. *)
  let param_tvar_erased =
    let this = param_index in
    let rec mentions j = function
      | Core.Type.Variable {variable = j'; _} -> j = j'
      | Core.Type.Global_app {type_arguments = ts; _} -> List.exists (mentions j) ts
      | Core.Type.Variable_app {head = h; arguments = ts} -> h = j || List.exists (mentions j) ts
      | Core.Type.Arrow {parameter = a; result = b} -> mentions j a || mentions j b
      | Core.Type.Meta {contents = Some t} -> mentions j t
      | _ -> false
    in
    let tvar_arg_erased j =
      match Core_util.Var_types.find_tvar tys j with
      | Some t ->
        Type_util.has_erased_type_in_type
          (Translation_types.unfold_cpp_typedef env (Translation_types.cpp_of_core env t))
      | None -> false
    in
    match Param_pos.nth fn_param_core_tys_orig this with
    | Some (Core.Type.Variable {variable = j; _}) when tvar_arg_erased j ->
      List.exists
        (fun (k, orig) ->
          (not (Param_pos.equal k this))
          && param_states_type_args id orig
          && mentions j orig
          && Type_util.has_erased_type_in_type
               (Translation_types.unfold_cpp_typedef env
                  (Translation_types.cpp_of_core env (Core_util.Var_types.apply tys orig))))
        (Param_pos.positioned fn_param_core_tys_orig)
    | _ -> false
  in
  let arg_expected_ty =
    match core_arg with
    (* A lambda under a coercion is written against the slot all the
       same. *)
    | Core.Expr.Lambda _
    | Core.Expr.Coerce {value = Core.Expr.Lambda _; _}
    | Core.Expr.Boxed_value {value = Core.Expr.Lambda _; _}
    | Core.Expr.Lambda_group_barrier {value = Core.Expr.Lambda _; _} -> param_expected_at_declared_arity ()
    | _ ->
    ( match
        match Param_pos.nth fn_param_core_tys_orig param_index with
        | Some (Core.Type.Variable _) ->
          param_expected_at_declared_arity ()
        | _ -> None
      with
    | Some _ as t -> t
    | None ->
    ( match core_arg with
    | Core.Expr.Coerce _ | Core.Expr.Boxed_value _ | Core.Expr.Lambda_group_barrier _ -> param_expected_subst ()
    (* [Core.Expr.Global]: a bare function name handed over as a value may need
       re-currying.  Count the arrows in the callee's {e unsubstituted}
       parameter type: arrows past the point where the codomain becomes a
       type variable belong to the element type the callee is generic in,
       not to the callable it expects. *)
    | Core.Expr.Global _ -> param_expected_at fn_param_core_tys_orig param_index
    (* So may a local function, for the same reason. *)
    | Core.Expr.Bound_variable {index = j; occurrence = occ} when local_callable j occ ->
      param_expected_at fn_param_core_tys_orig param_index
    (* A partial application is a callable built here rather than named,
       and reaches the slot at the arity the callee declared the parameter
       at, for the same reason a lambda does. *)
    | Core.Expr.Apply _ -> param_expected_at_declared_arity ()
    (* A constructed value is spelled here for the first time, so only the
       slot can say how its type arguments are curried.  Everything else
       about the type the constructor's own annotation knows better: it
       carries this producer's instantiation, which the parameter type may
       have erased.  So take the currying and nothing else. *)
    | Core.Expr.Construct _ -> param_expected_recurried ()
    (* A match in argument position becomes an immediately-invoked lambda,
       whose branches have to agree on one return type -- and the branches
       are where a value is spelled for the first time, so nothing inside
       states it.  Only the slot does. *)
    | Core.Expr.Match _ -> param_expected_at_declared_arity ()
    | _ -> None ) )
  in
  (* Where the substituted parameter says nothing, the result may:
     [trigger (subevent ...)] at a tree of family [Sum1<...>] fixes
     [trigger]'s family, which is what its parameter -- the [subevent]
     call's result -- has to be. *)
  let arg_expected_ty =
    match
      ( Lazy.force result_tvar_map,
        Param_pos.nth fn_param_core_tys_orig param_index )
    with
    | (result_names, (_ :: _ as m)), Some pt -> (
      let d =
        Translation_types.cpp_ir_of_core_type env result_names (type_simpl pt)
        |> Translation_tvars.deapply_family_variables
        |> Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) ->
               match t with
               | Variable (Index (_, Some v) | Named v) -> (
                 match List.find_opt (fun (v', _) -> Id.equal v v') m with
                 | Some (_, t') -> t'
                 | None -> t )
               | t -> t )
      in
      match arg_expected_ty with
      (* No slot at all: the declaration's type is the slot, where it is
         one this scope can write. *)
      | None | Some Any ->
        ( match Translation_types.spell_in_scope d with
        | Some _ as t -> t
        | None -> arg_expected_ty )
      (* A slot erased inside: each erased part is filled from the
         declaration where it says; what the declaration still says in
         its own variables is no answer. *)
      | Some slot ->
        let scope = current_scope_type_names () in
        let d =
          Cpp_ir.Types.map
            (fun (t : Cpp_ir.Lowered.Type.t) ->
              match t with
              | Variable tv ->
                let id = Cpp_ir.Type.variable_spelled tv in
                if List.exists (Id.equal id) scope then t else Any
              | t -> t )
            d
        in
        Some (Type_util.refine_erased_by ~expected:d slot) )
    | _ -> arg_expected_ty
  in
  (* Only a parameter the carrier reaches: one that mentions a
     higher-kinded variable of the callee.  [interp_state]'s tree
     [itree E T] is at the source family [E], and filling its erased
     family with the monad's [BotE] turned the inner [interp] into one
     over the target family. *)
  let param_mentions_carrier =
    match Param_pos.nth fn_param_core_tys_orig param_index with
    | Some t ->
      let hk = declared_higher_kinded_tvars fn_core_ty in
      not (IntSet.is_empty (IntSet.inter hk (collect_tvars_set IntSet.empty t)))
    | None -> true
  in
  let arg_expected_ty =
    if not param_mentions_carrier then arg_expected_ty
    else
      List.fold_left
        (fun t b ->
          Option.map (refine_by_instance_family b) t )
        arg_expected_ty instance_families
  in
  (* A callable the callee deduces is called at the callee's instantiation,
     so it goes over unadapted -- a lambda, or a callable passed on, as a
     self-call forwards its own ({!deduces_callable}); and a lambda takes
     what it is given where the slot erases. *)
  let deduced_callable =
    Option.has_some (Param_pos.nth fn_param_core_tys_orig param_index)
    && deduces_callable id param_index
  in
  let arg_expected_ty =
    match core_arg with
    | (Core.Expr.Lambda _ | Core.Expr.Coerce {value = Core.Expr.Lambda _; _}
    | Core.Expr.Boxed_value {value = Core.Expr.Lambda _; _}
    | Core.Expr.Lambda_group_barrier {value = Core.Expr.Lambda _; _}) when deduced_callable ->
      Option.map deduce_erased_domains arg_expected_ty
    | _ -> arg_expected_ty
  in
  (* When the callee's declared parameter type is value-dependent and
     resolves to [std::any] (e.g. [syms_semty xs]), a concrete pair/tuple
     literal passed at this call site (e.g. [(n, (n, tt))] for a literal
     [xs]) must be DEEP-erased — every component boxed into [std::any] —
     so that the callee's generic body, which reconstructs the value via
     [any_cast<pair<any,any>>], can recover it.  The deep-erasing
     constructor path in [gen_expr_custom_cons] is normally driven by the
     enclosing function's erased return type, so it is reached here by
     treating this call argument as if it were itself in erased "return"
     position for the duration of its generation. *)
  (* Where the call writes the variable -- the dictionary stated it --
     nothing deduces it, and an argument boxed to agree with a deduction
     would only fail to convert. *)
  let param_written_by_call = param_tvar_erased && dictionary_filled in
  let param_resolves_to_any =
    (param_tvar_erased && not param_written_by_call)
    ||
    match param_core_ty with
    | Some core_ty -> Translation_erasure.core_erases_to_box env core_ty
    | None -> false
  in
  let ret =
    if param_resolves_to_any then Some (Any : Cpp_ir.Lowered.Type.t)
    (* An argument is not a tail position, so the enclosing function's
       return type does not describe it -- and what the parameter says
       does.  Left to {!Translation_coerce.position_cpp_ty}'s fallback, a match in argument
       position builds its branches at the type the {e call} returns.

       Only where the parameter's type can be written, though: installed
       as a return type it is written out, as the argument's own explicit
       template arguments among other places, and a type naming a skipped
       global renders there as a bare argument list -- [<std::any,
       <std::any, std::any>>].  Where it cannot be written the enclosing
       return type is not right, but it is spellable, and a parameter
       that answers in text no compiler takes has not answered. *)
    else
      match arg_expected_ty with
      | Some t when Type_util.has_no_cpp_spelling t ->
        current_cpp_return_type ()
      | t -> t
  in
  { index = param_index;
    param = param_core_ty;
    expected = arg_expected_ty;
    ret = ret;
    tvar_erased = param_tvar_erased;
    written_by_call = param_written_by_call;
    deduced_callable = deduced_callable;
    expected_subst = param_expected_subst () }

(** [lower_call ~caller ~slot ?expected_ty env use args]: the call [use]
    [args] in the declaration [caller], lowered against its callee before any
    of its arguments is -- its semantic half first, as Core planned it at
    the Core types its position states ({!Core_elaborate.instantiation}), then how its
    arguments meet the callee's parameters in C++ ({!plan_call}), and the
    template application planned and validated against the callee's ABI
    ({!call_type_args}).  Generating the arguments reads the result and
    decides neither. *)
let lower_call ~caller ~slot ?(expected_ty : Cpp_ir.Lowered.Type.t option) env (use : Core.Global_use.t) args =
  let id = use.callee in
  let lex = current_lexenv () in
  let inst =
    Core_elaborate.instantiation ~walk:(elaborations ()) ~lex ~expected_core:slot.Translation_slot.expected_core_ty
      ~stated_core:slot.Translation_slot.stated_core_ty ~caller ~scope:(!tctx).lexical.current_type_vars use args
  in
  let plan = plan_call ~lex ?expected_ty env inst in
  call_type_args ~caller ~lex ?expected_ty env id plan
    ~has_value_args:(inst.call.regular <> [])

(** What a reference to global [x], its type instantiated by [instantiate],
    evaluates to as it is printed.

    Usually that is simply the global's type.  The exception is a [%result]
    block template, which prints as an immediately invoked lambda: the block
    is the global's body {e run}, so the reference evaluates to the result,
    and the lambda has to be given that as its return type.

    A call node carries its result in its call signature ([Cpp_ir.Expr.Call.signature]); a bare
    reference has no call node, so the answer is recorded on the global
    itself.  Consumers must not re-derive it -- doing so means reading the
    uninstantiated scheme back out of the front-end table, answering
    [List<T1>] where [List<uint64_t>] was meant. *)
let glob_yields env x instantiate =
  match callee_core_type x with
  | None -> None
  | Some core_ty -> (
    let is_result_block =
      Table.to_inline x
      && match Table.find_custom_opt x with
         | Some tmpl -> (Cpp_ir.Foreign.template_of_text tmpl).form = Block
         | None -> false
    in
    let inst = instantiate core_ty in
    let value_ty = if is_result_block then core_codomain inst else inst in
    try Some (Translation_types.cpp_of_core env value_ty)
    with e when CErrors.noncritical e -> None )
