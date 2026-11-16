(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Coercions between representations: boxing into and recovering out of
    [std::any], and adapting a function value to the slot it goes into --
    [crane_erase_fn], eta-expansion, currying to an expected arity, the
    adapter lambdas these build. *)

open Base.Common
open Names
open Util
open Translation_state
open Base.Type_util
open Core_query

(** [recover_carrier_result ~fun_ty ~n_args ~want expr] converts a call whose
    declared result is a carrier applied to a type variable -- [M A], a
    {!Core.Type.Variable_app} -- into the same carrier at the element the position means.

    A dictionary stores its methods monomorphically, so such a result comes
    back at the erased element whatever the call's own arguments were, and only
    an elementwise conversion gets from [M<std::any>] to [M<Nat>].  [fun_ty] is
    the callee's Core function type, or [None] where the caller knows the
    question does not arise. *)
let recover_carrier_result ~fun_ty ~n_args ~(want : Cpp_ir.Lowered.Type.t option) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let carrier_result =
    match Option.map (core_codomain_after n_args) fun_ty with
    | Some (Some (Core.Type.Variable_app _)) -> true
    | _ -> false
  in
  match want with
  (* A reified monadic carrier is a [shared_ptr], not a container: it has no
     elements to walk, and getting from one element type to another is the
     reification path's business, not a cast's. *)
  | Some (Shared_pointer _) -> expr
  | Some want when carrier_result && not (Cpp_ir.Types.prints_as_any want) -> Container_cast (want, expr, false)
  | _ -> expr

(** Wrap [expr] in the [crane_erase_fn] runtime helper, adapting it to the
    erased representation [shape] names (see {!Cpp_ir.Expr.Erase_shape}). *)
let wrap_crane_erase_fn shape (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t = Erase_callable (shape, expr)

(** Re-instantiate a function value that is being adapted for an erased slot:
    the values it will be applied to reached that slot erased too -- a
    [list nat] argument is stored as [List<std::any>], not [List<uint64_t>] --
    so the function has to be taken at the erased instantiation, or the
    adapter would unbox to a shape nothing ever boxed. *)
let erased_fn_instantiation : Cpp_ir.Lowered.Expr.t -> Cpp_ir.Lowered.Expr.t = function
  | Entity (g, (_ :: _ as tys), xs) -> Entity (g, List.map (fun _ -> Cpp_ir.Type.Any) tys, xs)
  | e -> e

(** [adapter_params ~prefix dom] -- fresh parameters for an adapter lambda,
    one per domain type, in source order.

    An adapter is a lambda whose only job is to call something else with its
    own arguments passed along, so its parameters exist only to be named.
    [prefix] distinguishes the adapters from one another in the generated
    code, and is the caller's to choose. *)
let adapter_params ~prefix dom =
  List.mapi
    (fun i ty -> (ty, Some (Id.of_string (Printf.sprintf "%s%d" prefix i))))
    dom

(** An {!adapter_params} parameter read back as the argument to pass along. *)
let adapter_arg (_, id) : Cpp_ir.Lowered.Expr.t = Local (Option.get id)

(** Whether a position has stated a type concrete enough to recover a box into.
    A slot spelled [std::any] wants the box as it stands, and one still spelled
    as a template parameter has not been stated at all: an [any_cast] there
    would be a guess about an instantiation this site cannot see. *)
let states_unboxed_target into = not (Cpp_ir.Types.prints_as_any into || contains_tvar into)

(** The C++ type a position is being generated into: what it states
    ([expected], a generator's [?expected_ty]), and where it states nothing,
    the enclosing function's return type -- which a tail position lands in.
    The one place that precedence is written down, so that "the type this
    position expects" cannot mean the position at one site and the enclosing
    return type at another. *)
let position_cpp_ty cx (expected : Cpp_ir.Lowered.Type.t option) =
  match expected with
  | Some _ as t -> t
  | None -> current_cpp_return_type cx ()

(** A callable handed to a parameter the callee declared at one of its own
    type variables has to arrive under a name: a closure's type cannot be
    spelled, so it can never agree with the same type variable as deduced
    from another argument -- [f (nat -> nat) S []], where the list argument
    settles the variable on [std::function<uint64_t(uint64_t)>].
    [Cpp_ir.Expr.Function_value] gives the closure that very type, deduced from it.

    The parameter type must be the callee's own, before this call site's
    instantiation is substituted into it: it is the template parameter that
    C++ has to deduce, not what it should deduce to. *)
let name_fn_arg_for_tvar_param param_core_ty (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match (resolve_meta param_core_ty, expr) with
  | Core.Type.Variable _, Lambda _ -> Function_value expr
  | _ -> expr

(** [mk_arity_call ~params ~saturated args] applies a callee to [args], given
    in {e source} order, where the callee's declaration fixes its parameters
    to [params].  [saturated] builds the call, from exactly as many arguments
    as [params] has.

    A call site need not match that arity, and a flat call is wrong whichever
    way it misses.  Arguments past the arity apply to the call's {e result} --
    a binder instantiated at a function type, say -- rather than to the
    callee.  Arguments short of it leave a closure over the ones still to
    come, so the call is eta-expanded instead of emitted shorter than it is
    declared.

    Omit [params] where the declaration is not known: an empty list means a
    nullary callee, which is a different thing and applies every argument to
    the result. *)
let mk_arity_call ?(params : Cpp_ir.Lowered.Type.t list option)
    ~(saturated : Cpp_ir.Lowered.Expr.t list -> Cpp_ir.Lowered.Expr.t) args : Cpp_ir.Lowered.Expr.t =
  match params with
  | None -> saturated args
  | Some params ->
    let arity = List.length params in
    let given = List.length args in
    if given > arity then
      match List.filteri (fun i _ -> i >= arity) args with
      | [] -> saturated args
      | rest -> Cpp_ir.Build.call (saturated (List.filteri (fun i _ -> i < arity) args)) rest
    else if given < arity then
      let waiting = adapter_params ~prefix:"_sat" (List.filteri (fun i _ -> i >= given) params) in
      Cpp_ir.Build.lambda waiting None
        [Return (Some (saturated (args @ List.map adapter_arg waiting)))]
        ~capture:Stored
    else saturated args

(** Apply a callee recovered from a bare [std::any], one argument at a time.

    Nothing about a boxed callable says how many arguments it takes: the
    producer's lambda stops at the first codomain that erases, so a value of an
    opaque function type ([nfun 2], a type-level [Fixpoint]) is a chain of unary
    [std::function<std::any(std::any)>]s.  Handing it every argument at once
    would cast it to a signature it was never stored at. *)
let apply_erased_curried ?(box = false) (callee : Cpp_ir.Lowered.Expr.t) arg_exprs : Cpp_ir.Lowered.Expr.t =
  List.fold_left
    (fun (f : Cpp_ir.Lowered.Expr.t) a ->
      let a = if box then Cpp_erasure.converting_ctor Any [a] else a in
      match f with
      (* A callable boxed right here never lost its type: recovering it would
         be a cast straight back to what it already was. *)
      | Box (_, callable) -> Cpp_ir.Build.call callable [a]
      | _ -> Erased_call (f, a) )
    callee arg_exprs

(** Apply a callee whose static C++ type is the erased [std::any].  [std::any]
    is not callable, so the canonical [std::function<std::any(std::any...)>]
    adapter the producer stored via {!box_for_any_slot} is recovered with
    an [any_cast] and each argument is boxed.  The result is a [std::any]. *)
let apply_erased_callee callee arg_exprs =
  apply_erased_curried ~box:true callee arg_exprs

(** Adapt a callable produced with fewer parameters than its use site expects.
    A body like [fun f acc => f acc] is eta-reduced before it reaches here, so
    the lambda takes one argument where the slot's type takes two; the missing
    arguments are supplied by eta-expansion, applying what the shorter lambda
    returns to the arguments it did not take.

    [core_arity] is how many arguments the slot's Core type takes: a lambda
    that takes fewer than its C++ slot but as many as its Core type is curried
    on purpose, not shortened, and is left alone -- as is one whose body
    [returns_a_lambda], having spelled the remaining arguments out itself. *)
let eta_expand_to_expected ?(expected_ty : Cpp_ir.Lowered.Type.t option) ~core_arity ~returns_a_lambda ~arity
    (f : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match Option.map strip_cpp_ref_const expected_ty with
  | Some (Function (dom, _)) when arity > 0 && core_arity > arity && List.length dom > arity && not returns_a_lambda ->
    let params = adapter_params ~prefix:"_ee" dom in
    let taken = List.filteri (fun i _ -> i < arity) params in
    let rest = List.filteri (fun i _ -> i >= arity) params in
    let call = List.fold_left (fun acc group -> Cpp_ir.Build.call acc (List.map adapter_arg group)) f [taken; rest] in
    Cpp_ir.Build.lambda params None [Return (Some call)] ~capture:Stored
  | _ -> f

(** [coerce ?term ?from ~into expr] adapts [expr] across a representation
    boundary: it is the single place that decides between boxing, [any_cast],
    [crane_erase_fn] and doing nothing.

    It first classifies the source side as boxed, opaque, concrete or unknown,
    and then reads the answer off that.  The classification rests on
    {!Base.Type_util.is_boxed_type}, not on {!Cpp_ir.Types.prints_as_any}:
    an opaque type also prints as [std::any], but it is an admission that
    the representation is unknown, and nothing may be boxed or cast on the
    strength of it.  A boundary with an opaque type on either side is therefore
    left alone, for the representation-tolerant helpers in [crane_fn.h] to
    sort out at instantiation time.  The pointer dimension (bare value versus
    [shared_ptr]) is delegated to {!Translation_conversion.gen_type_conversion_expr}, which already
    handles it.

    Omit [from] where the value's C++ type is not tracked -- a freshly
    generated constructor argument, say.  The value is then taken to be
    concrete but unnamed, which licenses boxing it (boxing any value is
    well-formed) but never an [any_cast] out of it, which would be a claim
    about a representation we cannot see.

    [term] is the Core expression [expr] was generated from.  It is consulted
    only for the one question a missing [from] leaves open: whether the value
    is a function, and so has to be adapted by [crane_erase_fn] before it is
    boxed. *)
let rec coerce cx ?term ?(from : Cpp_ir.Lowered.Type.t option) ~(into : Cpp_ir.Lowered.Type.t)
  (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let source = Translation_erasure.classify_erasure cx from in
  let same_type = match from with Some f -> cpp_ty_eq f into | None -> false in
  if same_type || into = Void then expr
  else
    match source with
    (* Casting a box to a name that is itself the box is not a recovery but
       an [any_cast<std::any>], which only succeeds on a doubly-boxed value
       and otherwise throws. *)
    | `Boxed when Translation_erasure.spells_as_any cx into -> expr
    (* A closure built here is not a box, whatever its erased type says: what
       is boxed is what it returns -- [@id lit] eta-expanded, with [id : ID]
       erased to [std::any id(std::any)], read at [Endo<lit>].  Its returns
       are recovered at the codomain instead. *)
    | `Boxed when (match expr with Lambda _ -> true | _ -> false) -> (
      match (expr, Translation_types.unfold_cpp_typedef cx (empty_env ()) into) with
      | Lambda l, Function (_, cod) ->
        let rec at_returns : Cpp_ir.Lowered.Stmt.t -> Cpp_ir.Lowered.Stmt.t = function
          | Return (Some e) -> Return (Some (coerce cx ~from:Any ~into:cod e))
          | st -> Cpp_ir.Map.stmt (Cpp_ir.Map.make ~expr:Fun.id ~stmt:at_returns ~type_:Fun.id ()) st
        in
        Lambda
          { l with
            return_type =
              (match l.return_type with Some t when Cpp_ir.Types.prints_as_any t -> Some cod | r -> r);
            body = List.map at_returns l.body }
      | _ -> expr )
    (* Already recovered; a second cast would be reading the same box twice. *)
    | `Boxed -> (
      match expr with
      | Any_cast _ -> expr
      | _ -> (
        (* A list went into the box with its elements boxed, so that is the
           shape the cast has to name however concrete the context's element
           type is; the converting constructor then recovers each element. *)
        match Cpp_erasure.erased_list_shape into with
        (* A custom list has no converting constructor to unbox its elements
           with, so it stays at the flat shape until a consumer converts it. *)
        | Some (g, shape) when Base.Table.is_custom g -> Cpp_erasure.unbox shape expr
        | Some (_, shape) -> Cpp_erasure.converting_ctor into [Cpp_erasure.unbox shape expr]
        | None -> Cpp_erasure.unbox into expr ) )
    (* Nothing may be boxed or cast on the strength of an admission that the
       representation is unknown. *)
    | `Opaque -> expr
    | (`Unknown | `Concrete _) as concrete_source -> (
      let is_function_value =
        match concrete_source with
        | `Concrete (Function _) -> true
        | `Concrete _ -> false
        | `Unknown -> ( match term with Some t -> Translation_erasure.core_expr_is_function_value cx t | None -> false )
      in
      if is_boxed_type into then
        (* Boxing is not idempotent: [std::any] holding a [std::any] is a box
           no consumer opens twice. *)
        match expr with
        | Box (Any, _) | Any_cast (Any, _) -> expr
        | _ ->
          (* A closure does not survive as itself: the consumer recovers it with
             [any_cast<std::function<std::any(std::any...)>>], so it is adapted
             to that canonical shape first.  It is then boxed like any other
             value -- a custom constructor template such as [std::make_pair]
             deduces its field type from the argument, and an unboxed
             [std::function] would store [pair<any, function<any(any)>>] where
             the consumer expects [pair<any,any>]. *)
          let adapted =
            if is_function_value then wrap_crane_erase_fn Boxed_whole (erased_fn_instantiation expr) else expr
          in
          Cpp_erasure.converting_ctor Any [adapted]
      else
        match into with
        (* A slot that erased its domain -- a record field whose Rocq type is
           [dty -> nat] at a value-dependent [dty], so
           [std::function<uint64_t(std::any)>] -- does not accept a closure
           written at the concrete domain, nor a generic lambda (which has no
           signature to convert from).  It takes one through the same
           [crane_erase_fn] adapter an erased parameter uses, whether or not the
           result erased along with the arguments. *)
        | Function (_, cod) when is_function_value && erased_domain_fun_ty into ->
          wrap_crane_erase_fn (At_signature cod) expr
        (* The mirror image: a callable whose result erased -- a constant
           whose Rocq type hides its quantifier behind a type alias, or whose
           result a type index alone pins down -- reaching a slot that names
           that result concretely.  It is called through a lambda that gives
           each argument the shape the callable declares and recovers what it
           returns. *)
        | Function (dom, cod)
          when (not (Cpp_ir.Types.prints_as_any cod))
               &&
               match concrete_source with
               | `Concrete (Function (_, scod)) -> Cpp_ir.Types.prints_as_any scod
               | _ -> false ->
          let sdom, scod =
            match concrete_source with
            | `Concrete (Function (d, c)) -> (d, c)
            | _ -> ([], Any)
          in
          let params = adapter_params ~prefix:"_ue" dom in
          let args =
            List.mapi
              (fun i ((ty, _) as p) ->
                let into = Option.default Cpp_ir.Type.Any (List.nth_opt sdom i) in
                coerce cx ~from:ty ~into (adapter_arg p) )
              params
          in
          let call = coerce cx ~from:scod ~into:cod (Cpp_ir.Build.call expr args) in
          Cpp_ir.Build.lambda params None [Return (Some call)] ~capture:Stored
        | _ -> (
          match concrete_source with
          | `Concrete f when not (Cpp_ir.Types.prints_as_any into) ->
            Translation_conversion.gen_type_conversion_expr ~src_ty:f ~dst_ty:into expr
          | _ -> expr ) )

(** [regroup_crossing ~from ~into expr]: [expr], whose C++ type is [from],
    read at [into] where the two differ only in how their arrows are grouped
    ({!Cpp_ir.Types.arrow_site}) -- a value spelled where it was declared reaching
    a slot a type argument spells curried, or back.  [crane_convert] regroups
    every function the value holds ([crane_cast_to] for [crane::fn] of
    another arity).  A function value itself is not this: it reaches a slot
    through the adapter {!curry_value_to_expected} writes,
    whose type is the slot's. *)
let regroup_crossing ~(from : Cpp_ir.Lowered.Type.t) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let from = strip_cpp_ref_const from and into = strip_cpp_ref_const into in
  match (from, into) with
  | Function _, _ | _, Function _ -> expr
  | _ when from = into || not (Cpp_ir.Types.same_arrows from into) -> expr
  | _ when Cpp_ir.Types.prints_as_any from || Cpp_ir.Types.prints_as_any into -> expr
  | _ -> Convert (into, expr)

(** The C++ type the value [e] has where that is known without generating
    it: a variable's binder type as planned, a global value's declared type.
    [None] for anything else.  [agree] says when the planned and the
    recorded binder type give the caller one answer
    ({!Translation_binders.planned_binder_type_or_derive}). *)
let value_cpp_type cx ~agree env e =
  match strip_magic e with
  | Core.Expr.Bound_variable {index = j; occurrence = occ} ->
    Translation_binders.planned_binder_type_or_derive cx ~use:"value's type" ~agree env j occ
  | Core.Expr.Global ({callee = r; _} as use) when Base.Core_util.Var_types.is_empty (Base.Core_util.written_type_args use) ->
    Option.map (Translation_types.cpp_of_core cx env) (callee_core_type cx r)
  | _ -> None

(** Whether a coercion is one the Rocq indices rule out, rather than one C++
    can perform.

    Extraction records [Core.Expr.Coerce (unit, nat, _, _)] for the [vnil] branch of a match
    on [vec (S n)] whose [return] clause computes [unit] there: a branch whose
    type differs from the type the match was instantiated at is one the
    scrutinee's index makes impossible.  [unit] is where this shows up
    unambiguously -- it carries no information, so no value of it can be
    converted to anything else, and a position holding one at another type can
    only be a position that is never reached.  What it returns is immaterial,
    and the only thing writable at an impossible type is an abort.

    The mirror is {!Gen_functions.dead_unit_returns_to_abort}, which catches the
    same branch where extraction recorded no coercion at all and a bare [tt]
    reaches a [return]; both throw {!Translation_cpp_build.dead_branch_message}. *)
let absurd_coercion cx from (into : Cpp_ir.Lowered.Type.t) =
  Base.Type_util.core_type_is_unit from
  && (not (is_cpp_unit_type into))
  && into <> Void
  && not (Translation_types.resolves_to_any_type cx into)

(** A list computed at a concrete element type (a call's result, a variable)
    going into a [Family_box] slot ([den t]): the family's generic consumers
    read it with every level boxed in turn -- its elements, and their
    components and elements -- so it is boxed at that shape
    ([crane_deep_box]), whatever container the [list] mapping makes it.  A
    literal needs no conversion, being built at the erased shape already (its
    slot is [Boxed]). *)
let deep_box_list cx e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match strip_magic e with
  | Core.Expr.Construct _ -> expr
  | e -> (
    match
      Option.bind (infer_core_body_type e) (fun t ->
          Cpp_erasure.erased_list_shape (Translation_types.cpp_of_core cx (empty_env ()) t) )
    with
    | Some _ -> Cpp_ir.Build.call (Runtime Cpp_ir.Crane_rt.Deep_box) [expr]
    | None -> expr )

(** Adapt a value being stored into a boxed slot of kind [kind] to the shape
    its consumers read back out of the box.  A function value is read with
    [any_cast<std::function<std::any(std::any)>>], which is what the
    [crane_erase_fn] runtime helper builds, deducing the callable's signature
    with [std::function] CTAD; a list in a [Family_box], by
    {!deep_box_list}.  A [Var_box] -- an existential's payload -- is read at
    whatever type its consumer knows, and keeps any other value as it is, as
    does a callable already adapted. *)
let box_for_any_slot cx kind e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match expr with
  | Erase_callable _ -> expr
  | _ when Translation_erasure.core_expr_is_function_value cx e -> wrap_crane_erase_fn Boxed_whole expr
  | _ -> ( match kind with Family_box -> deep_box_list cx e expr | Var_box -> expr )

(** [recover_boxed_component into e] opens the box when [e] is evidently a
    component read out of a pair that was recovered from one.  The context's
    type [into] is what the value is declared to be; the emitted expression is
    the evidence that it is physically a [std::any]. *)
let recover_boxed_component cx into (e : Cpp_ir.Lowered.Expr.t) =
  if Translation_erasure.yields_boxed_component e then coerce cx ~from:Any ~into e else e

(** [unbox_value into e] recovers [e], a value known to come out of a box, at
    [into]: {!coerce} from [std::any]. *)
let unbox_value cx into (e : Cpp_ir.Lowered.Expr.t) = coerce cx ~from:Any ~into e

(** [recover_boxed_result ~boxed ~expected expr] casts the result of a call
    back into the type the position expects -- see {!position_cpp_ty} -- when
    [boxed]
    says the callee hands back a [std::any] whatever its Core type claims,
    because its codomain erases or because it was itself recovered from a box
    and so goes through the canonical [std::function<std::any(std::any...)>]
    adapter.

    [boxed] is a statement about the callee, not a guess, so the recovery is
    unconditional: unlike {!unbox_into} it casts at a template parameter too,
    which inside a template is the one name the result has. *)
let recover_boxed_result cx ~boxed ~expected expr =
  match position_cpp_ty cx expected with
  | Some into when boxed -> coerce cx ~from:Any ~into expr
  | _ -> expr

(** [unbox_into into e] recovers [e] from its box at [into], where the
    position stated a type to recover it at, and leaves it boxed otherwise. *)
let unbox_into cx into e =
  match into with
  | Some into when states_unboxed_target into -> coerce cx ~from:Any ~into e
  | _ -> e

(** An {!adapter_params} parameter read back as the argument to pass along. *)

(** [apply_at_site site f args]: [f] applied to [args] as a callee spelled
    at the arrow site [site] takes them -- all at once where it was declared
    with them, one at a time through a type variable, and past the [n] a
    declaration wrote one at a time.  No arguments is [f] itself. *)
let apply_at_site (site : Cpp_ir.Types.arrow_site) (f : Cpp_ir.Lowered.Expr.t) args =
  let apply f args = match args with [] -> f | _ -> Cpp_ir.Build.call f args in
  let one_at_a_time f args = List.fold_left (fun f a -> Cpp_ir.Build.call f [a]) f args in
  match site with
  | Cpp_ir.Types.Declared -> apply f args
  | Cpp_ir.Types.Through_tvar | Cpp_ir.Types.Declared_at 0 -> one_at_a_time f args
  | Cpp_ir.Types.Declared_at n ->
    if List.length args <= n then apply f args
    else
      one_at_a_time
        (Cpp_ir.Build.call f (List.filteri (fun i _ -> i < n) args))
        (List.filteri (fun i _ -> i >= n) args)

(** [stored_adapter params e]: the lambda taking [params], in source order,
    that returns [e] and holds its captures by copy, its return type
    deduced. *)
let stored_adapter params (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  Lambda
    { params;
      type_params = [];
      return_type = None;
      body = [Return (Some e)];
      capture = Stored;
      moved = [];
      binders = [];
      fixpoint = None }

(** Make a global named in value position into an expression a caller can
    invoke, by eta-expanding it into a lambda that calls it.

    Two declarations need this.  A definition returning a closure ([nat -> nat
    -> nat] read as [nat -> (nat -> nat)]) is declared flat, with every arrow
    becoming a C++ parameter; that suits a direct call, but handing the bare
    name to something expecting a one-argument callable does not compile, so
    the nesting the use site asks for is rebuilt:

    {v [](uint64_t _ec0) { return [=](uint64_t _ec1) { return f(_ec0, _ec1); }; } v}

    A definition with a function-typed parameter is declared as a template
    deducing that parameter ({!Base.Common.fun_tparam_name}), and its name alone is
    an overload set rather than a value; one flat lambda gives the call the
    argument it deduces from:

    {v [](std::function<uint64_t(uint64_t)> _ec0, uint64_t _ec1) { return f(_ec0, _ec1); } v}

    A class method projected through its instance ([opN::op]) is a function
    named the same way, and is curried the same way: {!curry_value_to_expected}
    takes the callee's Core type rather than its name.

    [callee_site] is the arrow site the callee is spelled at
    ({!Cpp_ir.Types.arrow_site}), where [core_ty] is an instantiation of it: an
    instantiation can push arrows into the codomain ([idf {A} : A -> A] at
    [A := nat -> nat] reads as two arguments), and the declaration takes only
    the arguments it wrote, the rest going to what the call returns one at a
    time ([Declared_at n]).

    Returns [cglob] unchanged when the declaration is already a value. *)
let curry_value_to_expected cx env ?(expected_ty : Cpp_ir.Lowered.Type.t option) ?(callee_site = Cpp_ir.Types.Declared)
  ?(exact = false) core_ty
    (cglob : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let decl_dom =
    match Option.map (Translation_types.cpp_of_core cx env) core_ty with
    | Some (Function (dom, _)) -> dom
    | _ -> []
  in
  (* Number of parameters the outer lambda takes; the rest, if any, go into a
     nested one.  Only the arity comes from [exp_dom]; the types come from the
     declaration, which is concrete where the callee's signature may still be
     generic. *)
  let n_outer =
    match expected_ty with
    | Some (Function (exp_dom, _))
      when exp_dom <> [] && List.length decl_dom > List.length exp_dom ->
      Some (List.length exp_dom)
    | _ when List.exists (function Cpp_ir.Type.Function _ -> true | _ -> false) decl_dom ->
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
          (fun (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
            match ty with
            | Function _ when has_tany_in_type ty -> Reference (Forwarding, Auto)
            | _ -> ty )
          decl_dom
    in
    let params = adapter_params ~prefix:"_ec" decl_dom in
    let call = apply_at_site callee_site cglob (List.map adapter_arg params) in
    (* One lambda per group of arguments the slot takes at a time, as deep as
       it nests: [fn<fn<fn<R(C)>(B)>(A)>] takes [A], then [B], then [C]. *)
    let rec nest params (expected : Cpp_ir.Lowered.Type.t option) =
      match expected with
      | Some (Const t | Reference (_, t)) -> nest params (Some t)
      | Some (Function (dom, cod)) when dom <> [] && List.length params > List.length dom ->
        let k = List.length dom in
        stored_adapter
          (List.filteri (fun i _ -> i < k) params)
          (nest (List.filteri (fun i _ -> i >= k) params) (Some cod))
      | _ -> stored_adapter params call
    in
    nest params (if n_outer < List.length params then expected_ty else None)

(** The mirror of {!recover_carrier_result}: a value reaching a parameter the
    callee declared as a carrier applied to a type variable -- [M A], a
    {!Core.Type.Variable_app} -- arrives at whatever element the caller had, while a
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
let convert_carrier_arg cx param_core_ty (param_cpp_ty : Cpp_ir.Lowered.Type.t) e (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let elem_is_erased =
    match param_cpp_ty with
    | Apply (_, args) -> List.exists Cpp_ir.Types.prints_as_any args
    | _ -> false
  in
  match resolve_meta param_core_ty with
  | Core.Type.Variable_app _
    when (not (Cpp_ir.Types.prints_as_any param_cpp_ty))
         && elem_is_erased
         && (not (Translation_erasure.core_expr_is_function_value cx e))
         && (match param_cpp_ty with Function _ -> false | _ -> true) ->
    Cpp_ir.Expr.Convert (param_cpp_ty, expr)
  | _ -> expr

(** [erase_fn_arg_for_param env param_ty e expr] wraps a function-valued
    argument when the callee's parameter type is the canonical erased
    [std::function<std::any(std::any...)>] adapter (e.g. a class method
    polymorphic in its own type argument, [forall A, (A -> A) -> A -> A]):
    a concrete closure does not convert to the erased signature. *)
let erase_fn_arg_for_param cx env param_core_ty e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let open Cpp_ir.Expr.Erase_shape in
  (* The callee has already written this parameter down, so any opaque type in
     it has been spelled [std::any] in the header and the slot really is
     boxed. *)
  let param_cpp_ty = materialise_opaque (Translation_types.cpp_of_core cx env param_core_ty) in
  let erased_fn_param =
    match param_cpp_ty with
    (* An erased domain takes the adapter, at whatever result the signature
       kept: a parameter that erases only its ARGUMENTS (e.g.
       [std::function<typename I::M(std::any)>] for a higher-kinded class
       method) keeps that result type, since erasing it too would box the
       result twice. *)
    | Function (dom, cod)
      when List.exists (fun t -> Cpp_ir.Types.prints_as_any t || names_erased_alias t) dom ->
      Some (At_signature (if Cpp_ir.Types.prints_as_any cod then Any else cod))
    | Function (_, Any) -> Some (At_signature Any)
    (* The whole parameter is boxed -- a type-level [Fixpoint] landing on
       [using sem = std::any], say.  A callee that applies such a value goes
       through the canonical [std::function<std::any(std::any)>] adapter,
       so a raw closure dropped into the [std::any] would not match the cast
       that reads it back out. *)
    | ty when Translation_types.resolves_to_any_type cx ty -> Some Boxed_whole
    | _ -> None
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
        match resolve_meta t with
        | Core.Type.Global_app {head = r; type_arguments = args; _} ->
          Translation_erasure.value_indexed_family r || List.exists mentions_family args
        | Core.Type.Arrow {parameter = a; result = b} -> mentions_family a || mentions_family b
        | Core.Type.Variable_app {arguments = args; _} -> List.exists mentions_family args
        | _ -> false
      in
      match expand_core_fun_alias param_core_ty with
      | Core.Type.Arrow _ as t
        when List.exists mentions_family (core_domains t) ->
        let cod = core_codomain t in
        if mentions_family cod then Some (At_signature Any)
        else Some (At_signature (Translation_types.cpp_of_core cx env cod))
      | _ -> None )
  in
  match erased_fn_param with
  | Some shape when Translation_erasure.core_expr_is_function_value cx e -> Cpp_ir.Expr.Erase_callable (shape, expr)
  | _ -> convert_carrier_arg cx param_core_ty param_cpp_ty e expr
