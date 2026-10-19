(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Call planning for translation: the template arguments a call is written
    with, how arguments meet their parameters, the signature recorded on a
    call node, and calls through type-class instances. *)

open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Util
open Translation_state
open Ml_type_util
open Translation_support
open Translation_types

(** Make a global named in value position into an expression a caller can
    invoke, by eta-expanding it into a lambda that calls it.

    Two declarations need this.  A definition returning a closure ([nat -> nat
    -> nat] read as [nat -> (nat -> nat)]) is declared flat, with every arrow
    becoming a C++ parameter; that suits a direct call, but handing the bare
    name to something expecting a one-argument callable does not compile, so
    the nesting the use site asks for is rebuilt:

    {v [](uint64_t _ec0) { return [=](uint64_t _ec1) { return f(_ec0, _ec1); }; } v}

    A definition with a function-typed parameter is declared as a template
    deducing that parameter ({!Common.fun_tparam_name}), and its name alone is
    an overload set rather than a value; one flat lambda gives the call the
    argument it deduces from:

    {v [](std::function<uint64_t(uint64_t)> _ec0, uint64_t _ec1) { return f(_ec0, _ec1); } v}

    A class method projected through its instance ([opN::op]) is a function
    named the same way, and is curried the same way: {!curry_value_to_expected}
    takes the callee's ML type rather than its name.

    [callee_site] is the arrow site the callee is spelled at
    ({!Minicpp.arrow_site}), where [ml_ty] is an instantiation of it: an
    instantiation can push arrows into the codomain ([idf {A} : A -> A] at
    [A := nat -> nat] reads as two arguments), and the declaration takes only
    the arguments it wrote, the rest going to what the call returns one at a
    time ([Declared_at n]).

    Returns [cglob] unchanged when the declaration is already a value. *)
let curry_value_to_expected env ?expected_ty ?(callee_site = Declared) ?(exact = false) ml_ty cglob =
  let decl_dom =
    match Option.map (cpp_of_ml env) ml_ty with
    | Some (Tfun (dom, _)) -> dom
    | _ -> []
  in
  (* Number of parameters the outer lambda takes; the rest, if any, go into a
     nested one.  Only the arity comes from [exp_dom]; the types come from the
     declaration, which is concrete where the callee's signature may still be
     generic. *)
  let n_outer =
    match expected_ty with
    | Some (Tfun (exp_dom, _))
      when exp_dom <> [] && List.length decl_dom > List.length exp_dom ->
      Some (List.length exp_dom)
    | _ when List.exists (function Tfun _ -> true | _ -> false) decl_dom ->
      Some (List.length decl_dom)
    | _ -> None
  in
  match n_outer with
  | None -> cglob
  | Some n_outer ->
    (* The two groups share one numbering, so they are named together and
       then split. *)
    (* A function-typed parameter with erased positions in it takes a
       polymorphic function object, not the [std::function] its erasure
       spells: writing that type here would fix the very type argument the
       callee leaves to the caller.  [auto &&] passes whatever arrives
       through, which is all this adapter does with it -- unless [exact]: a
       value converted on to the erased signature is fixed at it anyway, and a
       generic adapter has no signature to convert from. *)
    let decl_dom =
      if exact then decl_dom
      else
        List.map
          (fun ty ->
            match ty with
            | Tfun _ when has_tany_in_type ty -> rval_ref Tauto
            | _ -> ty )
          decl_dom
    in
    let params = adapter_params ~prefix:"_ec" decl_dom in
    let call = apply_at_site callee_site cglob (List.map adapter_arg params) in
    (* One lambda per group of arguments the slot takes at a time, as deep as
       it nests: [fn<fn<fn<R(C)>(B)>(A)>] takes [A], then [B], then [C]. *)
    let rec nest params expected =
      match expected with
      | Some (Tconst t | Tref (_, t)) -> nest params (Some t)
      | Some (Tfun (dom, cod)) when dom <> [] && List.length params > List.length dom ->
        let k = List.length dom in
        mk_lambda
          (List.filteri (fun i _ -> i < k) params)
          None
          [Sreturn (Some (nest (List.filteri (fun i _ -> i >= k) params) (Some cod)))]
          ~capture:Closure
      | _ -> mk_lambda params None [Sreturn (Some call)] ~capture:Closure
    in
    nest params (if n_outer < List.length params then expected_ty else None)

(** The type of the global [use] names, at the type arguments the use wrote.
    An adapter's parameters are spelled in the caller's scope, so the
    callee's own type variables must not survive into them: this site's type
    arguments are what they stand for. *)
let instantiated_type use =
  Option.map
    (Mlutil.instantiate_written ~reader:"instantiated_type" use)
    (find_type_opt use.callee)

(** {!curry_value_to_expected} for the global [use] names. *)
let curry_to_expected env ?expected_ty use cglob =
  let decl_ty = find_type_opt use.callee in
  let ml_ty = instantiated_type use in
  let callee_site =
    match Option.map (cpp_of_ml env) decl_ty with
    | Some (Tfun (dom, _)) -> Declared_at (List.length dom)
    | _ -> Declared
  in
  curry_value_to_expected env ?expected_ty ~callee_site ml_ty cglob

(** The plan a call to [id] is written against: the head [id] was declared
    with, or, where it is not generated here, the conventions its call sites
    assume -- [instances] dictionaries first, then the variables it keeps up
    to the last one a call can reach, the leading phantoms among them, each
    at the kind its type demands. *)
let callee_abi ~instances id =
  let ml_ty = find_type_opt id in
  let hk = Option.cata declared_higher_kinded_tvars IntSet.empty ml_ty in
  let relaxed_tt = relaxed_tt_return_var id in
  let omitted = type_arg_omission id in
  Callable_abi.plan id ~scheme:(Mlutil.reference_scheme id) ~instances ~omitted
    ~higher_kinded:(fun v -> IntSet.mem (Scheme.Var.ordinal v) hk)
    ~kept:(fun v -> omitted v = None && relaxed_tt <> Some (Scheme.Var.ordinal v))
    ?reachable:(writable_tvar_count id)
    ~relaxed:(fun i ->
      IntSet.mem i (Option.cata Ml_type_util.relaxed_higher_kinded_tvars IntSet.empty ml_ty) )
    ~phantom_prefix:(leading_phantom_count id)

(** The explicit template arguments of a reference to [id] that is given a
    value for some of its variables, [by_var] pairing each variable with its
    C++ type: planned against [id]'s head, no dictionary among them. *)
let written_at_variables id by_var =
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
  lc_callee : GlobRef.t;
  lc_plan : call_plan;
  lc_callee_type : cpp_type;
  lc_written : Mlutil.Var_types.t;
  lc_abi : Callable_abi.t;
  lc_application : Template_application.t;
  lc_written_by_var : (Scheme.Var.t * cpp_type) list;
}

(** [call_type_args ~caller ?expected_ty env id plan args] -- the type
    arguments a call to [id] from the declaration [caller] writes, given its
    generated arguments: the dictionaries'
    first, then the regular ones that survive the erasure filters, recovered
    from the expected result, a dictionary or an argument where the filters
    left nothing.  Also the callee's instantiated C++ type and the
    instantiation the type arguments were read from, which the assembly
    needs. *)
let call_type_args ~caller ~lex ?expected_ty env id plan ~has_value_args =
  let args = if has_value_args then [()] else [] in
  let {
    cp_call = {Elaborated_call.primary = primary_ml_args; regular = regular_ml_args; _} as call;
    cp_instance_type_args = typeclass_type_args;
    cp_tyargs = tyargs;
    cp_fn_ml_ty_subst = fn_ml_ty_subst;
    cp_params = fn_param_ml_tys;
    cp_params_orig = fn_param_ml_tys_orig;
    cp_subst_index_of_orig = subst_index_of_orig;
    cp_tvars = tvars;
    cp_concrete_tvar_type = concrete_tvar_type;
    cp_result_tvar_map = result_tvar_map;
    _
  } = plan in
  let leading_params = Elaborated_call.leading_params call in
  let dictionary_filled = Elaborated_call.dictionary_filled call in
  (* The callee's variable its type spells [Tvar (_, i)]. *)
  let scheme_var i =
    Option.bind (Mlutil.reference_scheme id) (fun s -> Scheme.Var.of_tvar s i)
  in
  (* Whether [v] comes from a type binder of the callee's that erasure
     removed, as its schema records: what the call would pass there is a
     type, and nothing is passed. *)
  let schema = Mlutil.recorded_schema id in
  let erased_type_binder v =
    match Option.bind schema (fun s -> Ml_schema.origin s v) with
    | Some {Ml_schema.role = Ml_schema.Erased Miniml.Ktype; _} -> true
    | _ -> false
  in
  let ty = fn_ml_ty_subst in
  let ty = cpp_of_ml env ty in
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
  let tyargs = resolve_from_argument_types ~lex tyargs primary_ml_args in
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
    | Some ml_ty ->
      let hk = declared_higher_kinded_tvars ml_ty in
      (* A class's carrier -- the argument of a definitional class in a
         domain, [TFunctor T] -- and not a family, which is applied at an
         index its struct already leaves out. *)
      let class_carriers =
        List.fold_left
          (fun acc d ->
            match resolve_tmeta d with
            | Miniml.Tglob ((GlobRef.ConstRef _ as g), [ a ], _)
              when Typeclasses.is_class g -> (
              match resolve_tmeta a with
              | Miniml.Tapp (i, _) | Miniml.Tvar (_, i) -> IntSet.add i acc
              | _ -> acc )
            | _ -> acc )
          IntSet.empty (ml_domains ml_ty)
      in
      Hashtbl.fold
        (fun i _ acc ->
          if IntSet.mem i hk || not (IntSet.mem i class_carriers) then acc
          else IntSet.add i acc )
        (Ml_type_util.applied_ml_tvar_arities [ml_ty])
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
        Hashtbl.mem (Ml_type_util.applied_ml_tvar_arities [caller_ty]) j
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
    | Some ml_ty when IntSet.mem i plain_carriers ->
      let rec elements acc t =
        match resolve_tmeta t with
        | Miniml.Tapp (k, args) ->
          let acc = if k = i then args @ acc else acc in
          List.fold_left elements acc args
        | Miniml.Tglob (_, args, _) -> List.fold_left elements acc args
        | Miniml.Tarr (a, b) -> elements (elements acc a) b
        | _ -> acc
      in
      let element_args = elements [] (ml_codomain ml_ty) in
      let element_tys =
        List.filter_map
          (fun a ->
            match resolve_tmeta a with
            | Miniml.Tvar (_, j) -> (
              match Mlutil.Var_types.find_tvar tys j with
              | Some ty when not (Mlutil.isTdummy (resolve_tmeta ty)) ->
                let c = template_arg_of_ml_type ~site:Through_tvar env tvars ty in
                if prints_as_any c then None else Some c
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
            match resolve_tmeta a with
            | Miniml.Tvar _ -> false
            | _ -> true )
          element_args
      in
      if element_tys = [] then
        if element_erased_by_declaration
           && not (Ml_type_util.has_tany_written t')
        then None
        else Some t'
      else
        (* Compared unqualified: the same type reaches here spelled
           through its wrapper struct and without it. *)
        let rec norm t =
          map_cpp_type
            (function
              | Tnamespace (_, t) | Tconst t -> norm t
              | Tany | Topaque | Tvar (Tv_index (_, None)) -> Tany
              | Tvar (Tv_index (_, Some n) | Tv_named n)
                when not (List.exists (Id.equal n) (!tctx).current_type_vars) ->
                Tany
              | t -> t )
            t
        in
        let element_tys = List.map norm element_tys in
        let t'' =
          map_cpp_type
            (fun t -> if List.mem (norm t) element_tys then Tany else t)
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
    let unwrap = strip_param_spelling in
    List.find_map
      (fun (k, pt) ->
        match resolve_tmeta pt with
        | Miniml.Tglob ((GlobRef.ConstRef _ as g), [a], _)
          when Typeclasses.is_class g
               && ( match resolve_tmeta a with
                  | Miniml.Tapp (i', _) | Miniml.Tvar (_, i') -> i' = i
                  | _ -> false ) -> (
          (* What the call instantiated the class at, where that is known:
             the carrier composed and applied at the erased element. *)
          let from_instantiation =
            match subst_index_of_orig k with
            | Some ks -> (
              match Option.map resolve_tmeta (Param_pos.nth fn_param_ml_tys ks) with
              | Some (Miniml.Tglob (g', [x], _))
                when GlobRef.UserOrd.equal g g'
                     && not
                          (let rec has_class t =
                             match resolve_tmeta t with
                             | Miniml.Tglob (h, l, _) ->
                               Typeclasses.is_class h || List.exists has_class l
                             | Miniml.Tarr (a, b) -> has_class a || has_class b
                             | Miniml.Tapp (_, l) -> List.exists has_class l
                             | _ -> false
                           in
                           has_class x) ->
                let c = template_arg_of_ml_type ~site:Through_tvar env tvars x in
                (* A carrier is written at the erased element, so an
                   instantiation that erases nothing is some application
                   of it, not the carrier. *)
                ( match erase_carrier_elements i c with
                | Some c
                  when (not (prints_as_any c))
                       && Ml_type_util.has_tany_written c ->
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
              (List.nth_opt regular_ml_args)
          with
          | Some arg -> (
            match strip_magic arg with
            | MLrel j -> (
              match Option.map unwrap (binder_cpp_type_or_derive env j) with
              | Some (Tglob (g', [x], _)) when GlobRef.UserOrd.equal g g'
                && not (prints_as_any x) ->
                Some x
              | _ -> None )
            | _ -> None )
          | None -> None )
        | _ -> None )
      (Param_pos.positioned fn_param_ml_tys_orig)
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
      Option.cata (fun t -> Ml_type_util.higher_kinded_ml_tvars [t]) IntSet.empty
        (find_type_opt id)
    in
    fun i ty ->
      IntSet.mem i hk
      && (not (Mlutil.isTdummy (resolve_tmeta ty)))
      && (not (ml_type_contains_erased ty))
      && Mlutil.eq_ml_type (Mlutil.apply_ml_type ty [Miniml.Tunknown]) ty
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
    Mlutil.Var_types.bindings tys
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
             else template_arg_of_ml_type ~site:Through_tvar env tvars ty
           in
           (* A higher-kinded variable of the caller's reaching such a
              position is spelled as the template it is, which names no
              type; the position takes it at the erased element. *)
           let t =
             match (t, resolve_tmeta ty) with
             | (Tqualified _ | Tvar _), Miniml.Tvar (_, j)
               when IntSet.mem i plain_carriers && caller_higher_kinded j ->
               template_arg_of_ml_type ~site:Through_tvar env tvars
                 (Miniml.Tapp (j, [Miniml.Tunknown]))
             | _ when (prints_as_any t || under_applied_ind t)
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
             | Tvar (Tv_index (_, None)) ->
               Terased Ek_type
             | t when has_unnamed_tvar t -> Ml_type_util.resolve_tvars_to_any t
             | t -> t ) )
    |> List.filter (fun (v, t) -> not (mem v phantom_vars && prints_as_any t))
  in
  let regular_type_args = regular_of tys in
  (* Recover erased type args that C++ cannot deduce. Two cases: (a) tys is
     non-empty but all entries were erased (Tdummy Ktype) →
     filter_erased_type_args drops them all. (b) tys is empty — the Rocq
     extraction didn't supply type args at the call site, but the callee has
     Tdummy Ktype domain entries (erased type params).

     In both cases, if the callee's ML return type is a Tvar that refers to
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
      match (!tctx).current_cpp_return_type with
      | None -> None
      | Some ret_ty -> (
        match Option.map (fun t -> resolve_tmeta (ml_return_type t)) (find_type_opt id) with
        | Some (Miniml.Tvar (_, i)) -> (
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
      | Some ml_ty_orig, Some deducible -> (
        match resolve_tmeta (ml_return_type ml_ty_orig) with
        | Miniml.Tvar (_, i) -> not (IntSet.mem i deducible)
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
      | Some ml_ty_orig, Some deducible ->
        let all =
          List.fold_left tvars_of IntSet.empty
            (resolve_tmeta (ml_return_type ml_ty_orig)
             :: List.map resolve_tmeta (ml_domains ml_ty_orig))
        in
        not (IntSet.subset all deducible)
      | _ -> false
    in
    (* A higher-kinded argument is a type constructor, and [std::any] is not
       a spelling of one: a call reading one erased cannot be written out at
       all, so it keeps deducing -- whether or not its head declares a
       parameter there, as it does not for a result family it leaves to
       deduction.  Higher-kinded as the declaration has it
       ({!Ml_type_util.higher_kinded_ml_tvars}), not merely applied: an event
       family is applied everywhere it occurs and is still declared a plain
       [typename]. *)
    let no_erased_hkt_arg () =
      match find_type_opt id with
      | None -> true
      | Some ml_ty ->
        let hk = declared_higher_kinded_tvars ml_ty in
        not
          (List.exists
             (fun (v, t) -> IntSet.mem (Scheme.Var.ordinal v) hk && prints_as_any t)
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
         ({!under_applied_ind}) is filled the same way. *)
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
            if prints_as_any t || under_applied_ind t then
              match bound () with
              | Some (_, t') -> t'
              | None -> t
            (* Erased only in part -- a carrier [fun T => option (exp T)]
               written [std::optional<std::any>] -- the result fills the
               part it knows. *)
            else if Ml_type_util.has_tany_written t then
              match bound () with
              | Some (_, t') -> Ml_type_util.refine_erased_by ~expected:t' t
              | None -> t
            else t ) )
        targs
    in
    let written_out () =
      if some_tvar_undeducible () && no_erased_hkt_arg () then
        filter_erased_keyed ~preserve_positions:true
          (from_expected
             (regular_of
                (Call_tyargs.by_variable (resolve_from_argument_heads ~lex tyargs primary_ml_args)) ) )
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
        |> List.filter (fun (_, t) -> not (prints_as_any t))
      | None -> written_out ()
    else if Mlutil.Var_types.is_empty tys then
      (* Case (b): tys is empty — synthesize type args from scratch. Build one
         entry per Tdummy Ktype domain position.

         Recovery is attempted when:
         - [args = []] — no value args, so C++ can't deduce types.
         - [concrete_tvar_type <> None] — the callee's return type [Tvar]
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
          (List.filter erased_type_binder (Option.cata Ml_schema.vars [] schema))
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
      Option.cata (fun t -> Ml_type_util.higher_kinded_ml_tvars [t]) IntSet.empty
        (find_type_opt id)
    in
    List.map
      (fun (v, t) ->
        ( v,
          if (not (IntSet.mem (Scheme.Var.ordinal v) hk)) && under_applied_ind t then
            saturate_at_any t
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
        match dict_carrier_type_args env tvars id primary_ml_args with
        | Some [carrier] -> carrier_first carrier
        | _ ->
          (* Neither route knew the carrier.  An argument's type may still
             say what an erased plain type argument was, which is worth
             writing only here: filling a position is what would have taken
             the two routes above out of reach. *)
          build_type_args (resolve_from_argument_heads ~lex tyargs primary_ml_args) )
    else
      (* A list the call does write may still hold a family MiniML erased
         -- [translate inr1]'s source, taken off a morphism that erases it --
         which the argument constrained in it names.  Written erased, the
         argument is read at the erased family: converted node by node. *)
      (* Not where the family is an axiom: it has no struct to name. *)
      let no_struct f =
        match resolve_tmeta f with
        | Miniml.Tglob (g, _, _) ->
          Table.is_custom g
          || (match g with
              | GlobRef.IndRef _ -> false
              | GlobRef.ConstRef kn -> not (Option.has_some (Table.lookup_typedef_unchecked kn))
              | _ -> true)
        | _ -> false
      in
      let refined =
        resolve_from_argument_heads ~accept:(fun _ f -> not (no_struct f)) ~lex tyargs
          primary_ml_args
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
             when prints_as_any a && Call_tyargs.is_unwritten tyargs v ->
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
    lc_callee = id;
    lc_plan = plan;
    lc_callee_type = ty;
    lc_written = tys;
    lc_abi = abi;
    lc_application = application;
    lc_written_by_var = written_tvar_args;
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
let callee_result_bindings env id ~explicit expected =
  match (expected, find_type_opt id) with
  | Some exp, Some ml_ty ->
    let n = IntSet.fold max (collect_tvars_set IntSet.empty ml_ty) 0 in
    let names =
      List.init n (fun i -> Generated_name.indexed "R" (i + 1))
    in
    let cod =
      match convert_ml_type_to_cpp_type env names (type_simpl ml_ty) with
      | Tfun (_, c) -> c
      | t -> t
    in
    (* A family is written applied at an erased index and declared plain: in
       the pattern it is the variable itself. *)
    let cod = deapply_families cod in
    (* The enclosing function's result is this call's only where the call is
       what it returns, which nothing here says; a codomain with structure has
       to match it to count as evidence, a bare variable matches anything --
       [tfmap f (ops b)] inside [TFunctor_bundle] read [bundle<std::any>] for
       the list. *)
    let bare_cod = match cod with Tvar _ -> true | _ -> false in
    let exp =
      let as_fun t = unfold_cpp_typedef env (strip_param_spelling t) in
      match (as_fun exp, cod) with
      | Tfun (_, c), (Tglob _ | Tnamespace _) -> c
      | e, _ -> e
    in
    if (not explicit) && bare_cod then (names, [])
    else
      ( names,
        List.filter
          (fun (_, t) -> not (prints_as_any t))
          (extract_tvar_map cod (unfold_cpp_typedef env exp)) )
  | _ -> ([], [])

(** An instance's type argument extraction could not express -- a family
    that is a type-level lambda, [AllE := fun X => aE X + bE X] -- is erased
    from [ts], the instance's arguments.  A call's result says what it was:
    the instance's carrier ([box E] for [Monad_box]) heads the type the method
    returns, and its arguments are matched against the [expected] one's.
    [ts] instantiates the instance's variables in order, so position [k] is
    [Tvar (k + 1)], named [names.(k)] in the carrier pattern returned.  [None]
    where nothing is erased or nothing matches. *)
let instance_family_binding env r ts expected =
  let erased t = Mlutil.isTdummy (resolve_tmeta t) in
  match (expected, find_type_opt r) with
  | Some exp, Some inst_ty
    when List.exists (fun (_, t) -> erased t) (Mlutil.Var_types.bindings ts) -> (
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
      match resolve_tmeta (ml_codomain inst_ty) with
      | Miniml.Tglob (c, carrier :: _, _) when Table.is_typeclass c -> Some carrier
      | Miniml.Tglob _ as cod -> Some cod
      | _ -> None
    with
    | Some carrier -> (
      (* A family is written applied until it is deapplied: in the pattern
         it is the variable itself. *)
      let carrier =
        Ml_type_util.unqualify_ty
          (deapply_families (convert_ml_type_to_cpp_type env names carrier))
      in
      match (carrier, Ml_type_util.unqualify_ty (unfold_cpp_typedef env exp)) with
      | Tglob (h1, cargs, _), Tglob (h2, eargs, _)
        when GlobRef.CanOrd.equal h1 h2 && List.length cargs <= List.length eargs ->
        let m =
          List.filter
            (fun (_, t) -> not (prints_as_any t))
            (List.concat
               (List.map2 extract_tvar_map cargs
                  (safe_firstn (List.length cargs) eargs) ) )
        in
        if m = [] then None else Some (carrier, names, m)
      | _ -> None )
    | _ -> None )
  | _ -> None

let rec ml_arg_to_template_type ?expected env ml_arg =
  (* [None] for skipped infrastructure (ReSum instances, say): it is passed
     as a dictionary, so it is told apart from the regular arguments, but it
     has no struct and so no type to write.

     The type arguments an instance's generated struct has parameters for.

     Its declaration mints one per parameter erasure left standing, so a type
     argument erasure removed has no position to be written at and an argument
     written for it overruns the template head -- [ParamsV<IPZ, std::any>]
     against [template <IPtr _tcI0> struct ParamsV].  Erased instance
     parameters are already gone from the application's arguments by the time
     this sees them; an erased {e type} parameter is still in the [MLglob]'s
     list, as [Tdummy], and this is where it leaves.

     {!Ml_type_util.filter_erased_type_args} is the same all-or-nothing filter
     a call applies to its own: a position is what gives the others their
     meaning, so one that cannot be written costs the list. *)
  (* The variables the instance's struct declares a template parameter for,
     in its head's order ({!Instance_methods.instance_tvars}), among those
     the use writes an argument for. *)
  let struct_vars r ts =
    let ty = find_type r in
    List.filter
      (fun j -> Mlutil.Var_types.find_tvar ts j <> None)
      (Instance_methods.instance_tvars ty (Instance_methods.class_type ty))
  in
  let instance_type_args r ts =
    filter_erased_type_args
      (build_template_params ~site:Through_tvar env []
         (List.filter_map (Mlutil.Var_types.find_tvar ts) (struct_vars r ts)) )
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
              if not (Mlutil.isTdummy (resolve_tmeta t)) then
                Some (List.hd (build_template_params ~site:Through_tvar env [] [t]))
              else
                Option.bind (List.nth_opt names (j - 1)) (fun v ->
                    Option.map snd (List.find_opt (fun (v', _) -> Id.equal v v') m) ) ) )
          (Mlutil.Var_types.bindings ts)
      in
      if List.for_all (fun (_, o) -> o <> None) filled then
        Some
          (List.filter_map
             (fun j -> match List.assoc_opt j filled with Some o -> o | None -> None)
             (struct_vars r ts) )
      else None
  in
  match strip_dictionary ml_arg with
  | MLglob ({callee = r; _} as use) ->
    let ts = Mlutil.written_type_args use in
    if ref_returns_skipped r then None
    else
      (* Use the instance struct as a type - convert to Tglob *)
      Some
        (Tglob
           ( r,
             ( match instance_type_args_from_expected r ts with
             | Some args -> args
             | None -> instance_type_args r ts ),
             [] ))
  | MLrel i ->
    (* The instance is a lambda parameter - look up its name in the env and
       create a Tvar reference to the template parameter *)
    let db, _ = env in
    let name = List.nth db (pred i) in
    Some (named_tvar name)
  | MLapp (MLglob {callee = r; _}, _) when ref_returns_skipped r -> None
  | MLapp (MLglob ({callee = r; _} as use), inner_args) ->
    let ts = Mlutil.written_type_args use in
    (* Parameterized instance application, e.g. numList A H. Convert to
       Tglob(r, template_args, []) where template_args are built from the
       inner args. *)
    let template_args =
      List.filter_map
        (fun arg ->
          match arg with
          | MLdummy _ -> None (* Erased type param — skip *)
          | _ -> ml_arg_to_template_type env arg )
        inner_args
    in
    (* Instance parameters come first in the generated struct's template
       list ([template <typename _tcI0, typename T1>]), so the instance
       arguments must precede the type arguments here too. *)
    Some (Tglob (r, template_args @ instance_type_args r ts, []))
  | MLcase (_, scrutinee, branches)
    when Array.length branches = 1 ->
    (* Record field projection — e.g., [base_category(PS)].
       Resolve to [Tqualified(scrutinee_type, field_name)]. *)
    let (binds, _, _, br_body) = branches.(0) in
    Option.map
      (fun base_ty ->
        match br_body with
        | MLrel j when j >= 1 && j <= List.length binds -> (
          let idx = List.length binds - j in
          let field_id, _ = List.nth binds idx in
          match field_id with
          | Id name | Tmp name -> Tqualified (base_ty, name)
          | Dummy -> Tany )
        | _ -> Tany )
      (ml_arg_to_template_type env scrutinee)
  | MLapp (f, args) ->
    (* Parameterized instance application with non-glob head.
       Resolve head, then add arg types. *)
    let arg_tys =
      List.filter_map
        (fun arg ->
          match arg with
          | MLdummy _ -> None
          | _ -> ( try ml_arg_to_template_type env arg with _ -> None ) )
        args
    in
    Option.map
      (function
        | Tglob (r, existing, es) -> Tglob (r, existing @ arg_tys, es)
        | head_ty -> head_ty )
      (ml_arg_to_template_type env f)
  | MLdummy _ -> Some Tany (* Should not happen at top level, but be safe *)
  | _ ->
    CErrors.anomaly
      (Pp.str
         "ml_arg_to_template_type: unexpected ML term after \
          is_typeclass_instance_arg filter" )

(** The mirror of {!recover_carrier_result}: a value reaching a parameter the
    callee declared as a carrier applied to a type variable -- [M A], a
    {!Miniml.Tapp} -- arrives at whatever element the caller had, while a
    dictionary stores its methods at the erased one.

    Letting C++ convert implicitly is not enough.  A Crane carrier has a
    generated converting constructor and crosses on its own, but a custom one
    need not: [std::optional<std::any>] accepts {e anything}, so the whole
    [std::optional<Nat>] goes into the box and the consumer's [any_cast<Nat>]
    throws.  Asking the helper is the same question the result side asks, and
    it is the identity where the two instantiations already agree.

    Only for a value.  A function reaching such a slot is the erasure question
    above, already answered there; a carrier's element walk applied to a
    closure is not a conversion but a compile error.

    And only where the element is erased, which is the whole of the mismatch:
    a carrier written at a concrete element is already the caller's own type,
    and naming it again buys nothing while asking the head to be spelled as a
    template -- which a declaration that kept it a phantom [typename] will not
    accept. *)
let convert_carrier_arg param_ml_ty param_cpp_ty e expr =
  let elem_is_erased =
    match param_cpp_ty with
    | Tapply (_, args) -> List.exists prints_as_any args
    | _ -> false
  in
  match resolve_tmeta param_ml_ty with
  | Miniml.Tapp _
    when (not (prints_as_any param_cpp_ty))
         && elem_is_erased
         && (not (ml_expr_is_function_value e))
         && classify_fun_erasure param_cpp_ty = Fe_not_a_function ->
    CPPconvert (param_cpp_ty, expr)
  | _ -> expr

(** [erase_fn_arg_for_param env param_ty e expr] wraps a function-valued
    argument when the callee's parameter type is the canonical erased
    [std::function<std::any(std::any...)>] adapter (e.g. a class method
    polymorphic in its own type argument, [forall A, (A -> A) -> A -> A]):
    a concrete closure does not convert to the erased signature. *)
let erase_fn_arg_for_param env param_ml_ty e expr =
  (* The callee has already written this parameter down, so any [Topaque] in
     it has been spelled [std::any] in the header and the slot really is
     boxed. *)
  let param_cpp_ty = materialise_opaque (cpp_of_ml env param_ml_ty) in
  let erased_fn_param =
    match classify_fun_erasure param_cpp_ty with
    (* An erased domain takes the adapter, at whatever result the signature
       kept: a parameter that erases only its ARGUMENTS (e.g.
       [std::function<typename I::M(std::any)>] for a higher-kinded class
       method) keeps that result type, since erasing it too would box the
       result twice. *)
    | Fe_erased_domain kept -> Some (At_signature (Option.default Tany kept))
    | Fe_concrete_domain | Fe_not_a_function -> (
      match param_cpp_ty with
      | Tfun (_, cod) when cod = Tany -> Some (At_signature Tany)
      (* The whole parameter is boxed -- a type-level [Fixpoint] landing on
         [using sem = std::any], say.  A callee that applies such a value goes
         through the canonical [std::function<std::any(std::any)>] adapter,
         so a raw closure dropped into the [std::any] would not match the cast
         that reads it back out. *)
      | ty when resolves_to_any_type ty -> Some Boxed_whole
      | _ -> None )
  in
  (* The instantiation this call sees may still hide an erasure the callee's
     declaration made: a functor's [S.sem a] -- a type family applied to a
     value -- is erased in [Make]'s body, and [Make<Inst>]'s call site reads it
     as [Inst::sem].  The parameter is declared at the erased domain. *)
  let erased_fn_param =
    match erased_fn_param with
    | Some _ -> erased_fn_param
    | None -> (
      let rec mentions_family t =
        match resolve_tmeta t with
        | Miniml.Tglob (r, args, _) ->
          value_indexed_family r || List.exists mentions_family args
        | Miniml.Tarr (a, b) -> mentions_family a || mentions_family b
        | Miniml.Tapp (_, args) -> List.exists mentions_family args
        | _ -> false
      in
      match expand_ml_fun_alias param_ml_ty with
      | Miniml.Tarr _ as t
        when List.exists mentions_family (ml_domains t) ->
        let cod = ml_codomain t in
        if mentions_family cod then Some (At_signature Tany)
        else Some (At_signature (cpp_of_ml env cod))
      | _ -> None )
  in
  match erased_fn_param with
  | Some shape when ml_expr_is_function_value e -> wrap_crane_erase_fn shape expr
  | _ -> convert_carrier_arg param_ml_ty param_cpp_ty e expr

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
    ({!generalises_callable}), its body read for the ones it holds on to. *)
let assumed_deduced_callables r b ty =
  let ids, _ = collect_typed_lams ty b in
  let binder_tys = List.rev_map snd ids in
  let ungeneralised = ungeneralised_callables_of_definition r ty b in
  let declared t = convert_ml_type_to_cpp_type (Common.empty_env ()) [] (type_simpl t) in
  match find_type_opt r with
  | None -> []
  | Some fn_ml_ty -> (
    match declared fn_ml_ty with
    | Tfun (dom, cod) ->
      let primary = primary_tvar_indices dom cod in
      List.filter_map
        (fun (pos, pt) ->
          match (declared pt, Param_pos.source_index binder_tys pos) with
          | (Tfun _ as f), Some i
            when generalises_callable ~kept_as_fn:(Escape.IntSet.mem i ungeneralised) ~primary f ->
            Some pos
          | _ -> None )
        (Param_pos.positioned (Param_pos.orig_params ~expand:expand_ml_fun_alias fn_ml_ty))
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
let deduce_erased_domains = function
  | Tfun (doms, cod) ->
    Tfun
      ( List.map
          (fun d -> if exists_cpp_type prints_as_any d then Tref (Lvalue, Tconst Tauto) else d)
          doms,
        cod )
  | t -> t

(** [record_call_sig env callee_ty e] records what the callee's ML type says
    about [e], when [e] is a call nothing has been recorded on yet.

    The application site is where the answer is known; the {!CPPfun_call} node
    is built further down, in {!eta_fun}, so the answer is stamped on here
    rather than threaded through every intermediate that only forwards it.  A
    callee with no ML type, or one that is not a call at all, keeps
    {!call_opaque}: a consumer must defer to C++ deduction rather than invent
    a type.

    Both fields come off the {e same} instantiated type, so a consumer reading
    one cannot be looking at a different callee than a consumer reading the
    other.  The parameter list is kept only when it has one entry per
    argument -- {!Minicpp.call_sig} enforces that -- since a partial
    application, or a callee whose arrows an eta-expansion has rearranged,
    would otherwise hand the printer a misaligned list. *)
let record_call_sig env callee_ty e =
  match (e, callee_ty) with
  | CPPfun_call ({cs_yields = Ropaque; cs_params = Punknown}, f, args),
    Some ml_ty ->
    let cpp_of ml = convert_ml_type_to_cpp_type env [] ml in
    ( match cpp_of (ml_codomain ml_ty) with
    | exception e' when CErrors.noncritical e' -> e
    | ty ->
      let params =
        try Some (List.map cpp_of (ml_value_domains ml_ty))
        with e' when CErrors.noncritical e' -> None
      in
      let sg =
        Minicpp.call_sig ~yields:ty ?params ~nargs:(List.length args.rev) ()
      in
      (* An over-application is a call of the call that took the callee's
         own arguments, and that one yields the callable the rest are applied
         to: what is left of the type once its arguments are taken. *)
      let f =
        match f with
        | CPPfun_call ({cs_yields = Ropaque; cs_params = Punknown}, g, inner_args)
          ->
          ( match
              cpp_of
                (Ml_type_util.ml_drop_arrows (List.length inner_args.rev) ml_ty)
            with
          | exception e' when CErrors.noncritical e' -> f
          | Tany | Topaque -> f
          | inner_ty ->
            CPPfun_call
              ( Minicpp.call_sig ~yields:inner_ty
                  ~nargs:(List.length inner_args.rev) (),
                g,
                inner_args ) )
        | f -> f
      in
      CPPfun_call (sg, f, args) )
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

(** [resolve_from_context ~lex ~slot call] -- the holes of [call]'s reading
    of its scheme variables that its context states: the ML types [slot]
    expects or states for its result, and the heads its arguments' types
    give a type-level function a domain names.  The rest of the elaboration
    ({!Core_elaborate.elaborate_arguments}) is fixed by the call alone. *)
let resolve_from_context ~lex ~slot (call : Elaborated_call.t) =
  let {Elaborated_call.callee = id; callee_type = fn_ml_ty; primary = primary_ml_args; tyargs; _} =
    call
  in
  (* An erased event family the position's type names: [memM_interp]'s [E],
     given unapplied where [on_mem] takes a handler into [itree BotE].  The
     family occurs in the callee's result only, where nothing deduces it and
     the phantom filler would write [void]. *)
  let tyargs =
    match
      match slot.expected_ml_ty with
      | Some _ as t -> t
      | None -> slot.stated_ml_ty
    with
    | Some result when Call_tyargs.interior_holes tyargs <> [] ->
      let families = Ml_type_util.event_family_ml_tvars [fn_ml_ty] in
      (* A family is a head, or one applied at the index it erases
         ([BotE _]); [box nat] met at a bare variable is a value type, not
         the family. *)
      let family_shaped b =
        match resolve_tmeta b with
        | Miniml.Tglob (_, [], _) -> true
        | Miniml.Tglob (_, args, _) ->
          Ml_type_util.is_ml_erased_ty (List.nth args (List.length args - 1))
        | _ -> false
      in
      (* With [~constructors]: an applied variable against an application
         is the head, which for a family -- the only variables filled here --
         is the answer. *)
      let found =
        tvar_instantiation_found ~lex ~constructors:true ~result
          fn_ml_ty primary_ml_args
      in
      (* Only where nothing deduces it: a family a parameter spells is the
         compiler's to read off the argument. *)
      let deducible =
        Option.default IntSet.empty (deducible_tvars_of_glob id)
      in
      Call_tyargs.resolve Call_tyargs.Expected_result
        (fun v ->
          let k = Scheme.Var.ordinal v in
          match List.assoc_opt k found with
          | Some b
            when IntSet.mem k families && (not (IntSet.mem k deducible))
                 && family_shaped b ->
            Some b
          | _ -> None )
        (Call_tyargs.interior_holes tyargs) tyargs
    | _ -> tyargs
  in

  (* A type-level function passed where a type alias in a domain names it
     -- the category's [C] in [Id_ obj C] -- is a hole of the reading, stated
     by the dictionary argument.  Filled before anything is substituted, so
     the parameter types the arguments are generated against and the
     explicit type arguments the call writes agree. *)
  Elaborated_call.with_tyargs call
    (resolve_from_argument_heads ~only_alias_args:true ~lex tyargs primary_ml_args)

(** [plan_call ~caller ?expected_ty env call] -- what the elaborated [call]
    from the declaration [caller] needs to know before its arguments are
    generated, beyond its elaboration: its scheme variables spelled in the
    caller's scope, the callee's parameter types at that instantiation, and
    the C++ types its result and its dictionaries are expected at.  Read by
    {!gen_call_args} and by the assembly in {!eta_fun}. *)
let plan_call ~caller ~lex ?expected_ty env (call : Elaborated_call.t) =
  let {
    Elaborated_call.callee = id;
    callee_type = fn_ml_ty;
    primary = primary_ml_args;
    excess = excess_args;
    instances = typeclass_ml_args;
    regular = regular_ml_args;
    tyargs;
    _
  } =
    call
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
          (find_type id) primary_ml_args
      with
      | [] -> None
      | found ->
        (* A carrier bound as a head partially applied ([itree TopE]) is
           applied by appending: the hole inside its family is the family's
           own erased index, not the argument the carrier is missing. *)
        let rec subst t =
          match resolve_tmeta t with
          | Miniml.Tvar (_, i) -> (
            match List.assoc_opt i found with Some b -> b | None -> t )
          | Miniml.Tapp (k, args) -> (
            let args = List.map subst args in
            match List.assoc_opt k found with
            | Some (Miniml.Tglob (g, fixed, l)) -> Miniml.Tglob (g, fixed @ args, l)
            | Some b -> Mlutil.apply_ml_type b args
            | None -> Miniml.Tapp (k, args) )
          | Miniml.Tglob (g, args, l) -> Miniml.Tglob (g, List.map subst args, l)
          | Miniml.Tarr (a, b) -> Miniml.Tarr (subst a, subst b)
          | t -> t
        in
        let t = cpp_of_ml env (subst (ml_codomain (find_type id))) in
        spell_in_scope t
    in
    match expected_result with
    | Some e when exists_cpp_type prints_as_any e -> (
      match from_args () with
      | Some a -> Some (Ml_type_util.refine_erased_by ~expected:a e)
      | None -> expected_result )
    (* With no expected type of its own the call may not be the enclosing
       function's result at all -- a let-bound computation over another
       family -- so what its arguments state comes before that result. *)
    | None -> (
      match from_args () with
      | Some _ as a -> a
      | None -> (!tctx).current_cpp_return_type )
    | _ -> expected_result
  in
  let typeclass_type_args =
    List.map
      (ml_arg_to_template_type ?expected:expected_result env)
      typeclass_ml_args
  in
  (* The families the call's instances were found to have: the slots their
     arguments are generated against erase them the same way. *)
  let instance_families =
    List.filter_map
      (fun a ->
        match strip_magic a with
        | MLglob ({callee = r; _} as use) ->
          instance_family_binding env r (Mlutil.written_type_args use)
            expected_result
        | _ -> None )
      typeclass_ml_args
  in
  (* A partial application is eta-expanded into a lambda spelled in the
     caller's scope, and a variable of the callee's that neither the call
     nor its arguments instantiate is not one of the caller's: left in, it
     prints as whichever caller variable shares its index -- [h_get]'s index
     as the enclosing handler's [T1].  It is erased, and a position nothing
     deduces is then written as the box it is. *)
  let tyargs =
    let n_params =
      let rec count ty =
        match expand_ml_fun_alias ty with
        | Miniml.Tarr (t, rest) ->
          (match resolve_tmeta t with
           | Miniml.Tdummy _ -> count rest
           | _ -> 1 + count rest)
        | _ -> 0
      in
      count fn_ml_ty
    in
    (* Only one the lambda's result spells: a variable the codomain does not
       mention -- a rank-2 handler's [forall X] -- is not the call's to
       instantiate, and keeps itself.  And not in a call to the declaration
       being generated, whose variables {e are} the caller's. *)
    let self_call =
      match caller with
      | Some r -> GlobRef.UserOrd.equal r id
      | None -> false
    in
    if self_call || List.length primary_ml_args >= n_params then tyargs
    else
      let tyargs = resolve_from_argument_types ~lex tyargs primary_ml_args in
      let in_cod = collect_tvars_set IntSet.empty (ml_codomain fn_ml_ty) in
      let open_vars = Call_tyargs.beyond_extent tyargs in
      match
        List.fold_left
          (fun m v ->
            let i = Scheme.Var.ordinal v in
            if IntSet.mem i in_cod then max m i else m )
          0 open_vars
      with
      | 0 -> tyargs
      | n ->
        (* Erased only where it would be misread: a variable whose spelling
           no caller variable has is bound by the eta-lambda itself (see
           [eta_tparams]), and deduced there from the parameter that names
           it -- [memM T2] of a natural transformation. *)
        let collides i =
          List.exists
            (fun v -> String.equal (Id.to_string v) (Minicpp.tvar_spelling i))
            (!tctx).current_type_vars
        in
        Call_tyargs.resolve Call_tyargs.Eta_parameter
          (fun v ->
            let i = Scheme.Var.ordinal v in
            Some
              ( if IntSet.mem i in_cod && collides i then Miniml.Tunknown
                else Miniml.Tvar (Miniml.Schematic, i) ) )
          (List.filter (fun v -> Scheme.Var.ordinal v <= n) open_vars)
          tyargs
  in
  let tys = Call_tyargs.by_variable tyargs in
  (* The one substitution that takes the callee's declared types to this
     call's; without it the argument generated into a [bind]'s [m A] is left
     with no stated type at all. *)
  let subst_ml_ty = instantiate_at_call id tys primary_ml_args in
  let fn_ml_ty_subst = subst_ml_ty fn_ml_ty in
  let fn_param_ml_tys =
    Param_pos.subst_params ~expand:expand_ml_fun_alias fn_ml_ty_subst
  in
  (* Non-substituted parameter types: used to detect whether a callback's
     codomain is a type variable (needs adapter wrapping) vs concrete unit
     (C++ definition already uses void in the is_invocable_v requires clause). *)
  let fn_param_ml_tys_orig =
    Param_pos.orig_params ~expand:expand_ml_fun_alias fn_ml_ty
  in
  (* The two lists above are not indexed alike: substitution can make a
     parameter dummy that was not one before, and from that parameter on a
     declared position is one place further left in the substituted list.
     A reader holding a declared position and wanting the substituted type
     there converts it here (see {!Param_pos}). *)
  let subst_index_of_orig =
    Param_pos.subst_of_orig
      ~erased:(fun t ->
        match resolve_tmeta (subst_ml_ty t) with
        | Miniml.Tdummy _ -> true
        | _ -> false )
      fn_param_ml_tys_orig
  in
  (* {b Concrete T1 for excess-arg calls.}  When [tys = []] and there
     are excess args, the callee's polymorphic return type [Tvar i] can't
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
    if (not (Mlutil.Var_types.is_empty tys)) || excess_args = [] then
      None
    else
      match (!tctx).current_cpp_return_type with
      | None -> None
      | Some ret_ty ->
        match find_type_opt id with
        | None -> None
        | Some ml_ty_orig ->
          let ret = Ml_type_util.resolve_tmeta (ml_return_type ml_ty_orig) in
          ( match ret with
          | Miniml.Tvar (_, _) ->
            (* The excess arguments' C++ types, where each is a parameter. *)
            let excess_cpp_tys =
              List.filter_map
                (fun ml_arg ->
                  match ml_arg with
                  | MLrel i -> Option.map (convert_ml_type_to_cpp_type env tvars) (parameter_type env i)
                  | _ -> None )
                excess_args
            in
            if List.length excess_cpp_tys = List.length excess_args then
              Some (Tfun (excess_cpp_tys, ret_ty))
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
      | MLglob {callee = r; _} ->
        List.filter_map (fun (var_name, ml_ty) ->
          let cpp_ty = cpp_of_ml env ml_ty in
          if prints_as_any cpp_ty then None
          else Some (var_name, cpp_ty)
        ) (Table.get_instance_promoted_types r)
      | _ -> []
    ) typeclass_ml_args
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
             | None -> (!tctx).current_cpp_return_type ) ) )
  in
  {
    cp_call = call;
    cp_expected_result = expected_result;
    cp_instance_type_args = typeclass_type_args;
    cp_instance_families = instance_families;
    cp_tyargs = tyargs;
    cp_tys = tys;
    cp_fn_ml_ty_subst = fn_ml_ty_subst;
    cp_params = fn_param_ml_tys;
    cp_params_orig = fn_param_ml_tys_orig;
    cp_subst_index_of_orig = subst_index_of_orig;
    cp_tvars = tvars;
    cp_concrete_tvar_type = concrete_tvar_type;
    cp_instance_promoted = instance_promoted_map;
    cp_result_tvar_map = result_tvar_map
  }

(** [lower_call ~caller ~slot ?expected_ty env use args]: the call [use]
    [args] in the declaration [caller], lowered against its callee before any
    of its arguments is -- how its arguments meet the callee's parameters
    ({!plan_call}), and the template application planned and validated
    against the callee's ABI ({!call_type_args}).  Generating the arguments
    reads the result and decides neither. *)
let lower_call ~caller ~slot ?expected_ty env use args =
  let id = use.callee in
  let lex = current_lexenv () in
  let call =
    resolve_from_context ~lex ~slot (Core_elaborate.elaboration ~lex use args)
  in
  let plan = plan_call ~caller ~lex ?expected_ty env call in
  call_type_args ~caller ~lex ?expected_ty env id plan ~has_value_args:(call.regular <> [])

(** What a reference to global [x], its type instantiated by [instantiate],
    evaluates to as it is printed.

    Usually that is simply the global's type.  The exception is a [%result]
    block template, which prints as an immediately invoked lambda: the block
    is the global's body {e run}, so the reference evaluates to the result,
    and the lambda has to be given that as its return type.

    A call node carries its result in its {!Minicpp.call_sig}; a bare
    reference has no call node, so the answer is recorded on the global
    itself.  Consumers must not re-derive it -- doing so means reading the
    uninstantiated scheme back out of the front-end table, answering
    [List<T1>] where [List<uint64_t>] was meant. *)
let glob_yields env x instantiate =
  match find_type_opt x with
  | None -> None
  | Some ml_ty -> (
    let is_result_block =
      Table.to_inline x
      && match Table.find_custom_opt x with
         | Some tmpl -> (Minicpp.inline_template tmpl).it_form = Block_iife
         | None -> false
    in
    let inst = instantiate ml_ty in
    let value_ty = if is_result_block then ml_codomain inst else inst in
    try Some (cpp_of_ml env value_ty)
    with e when CErrors.noncritical e -> None )
