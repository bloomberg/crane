(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Coercions between representations: boxing into and recovering out of
    [std::any], and adapting a function value to the slot it goes into --
    [crane_erase_fn], eta-expansion, currying to an expected arity, the
    adapter lambdas these build. *)

open Base.Common
open Names
open Util
open Lowering_state
open Base.Type_util
open Core_plan.Query

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

(** What {!decide} asks of the context: to unfold an alias, and whether a
    type is a box or spelled as one once aliases are followed. *)
type aliases = {
  unfold : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t;
  boxed_source : Cpp_ir.Lowered.Type.t -> bool;
  spells_as_any : Cpp_ir.Lowered.Type.t -> bool;
}

(** The aliases of the unit being lowered. *)
let aliases_in cx =
  (* A mapped inductive of no arguments is the C++ type its mapping names:
     [positive] and [N] mapped to [unsigned int] are one type. *)
  let scope = Lowering_state.get_current_type_vars cx in
  let hkt = Lowering_state.hkt_resolutions cx in
  let mapped (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
    match t with
    (* A variable standing for an instance's associated type is that type,
       as the body will be rewritten to say. *)
    | Variable (Index (i, _)) when List.mem_assoc i hkt -> List.assoc i hkt
    | Entity_application (g, [], _) when Base.Table.is_custom g -> (
      match Base.Table.find_custom_opt g with Some text -> External (text, []) | None -> t )
    (* A variable written by its index alone is the one the scope names
       at that index. *)
    | Variable (Index (i, None)) when i >= 1 -> (
      match List.nth_opt scope (i - 1) with Some n -> Variable (Index (i, Some n)) | None -> t )
    | t -> t
  in
  { unfold = (fun t -> mapped (Types.unfold_cpp_typedef cx (empty_env ()) (strip_cpp_ref_const t)));
    boxed_source = Erasure.is_boxed_source cx;
    spells_as_any = Erasure.spells_as_any cx }

(** No aliases followed: the types as written. *)
let as_written =
  { unfold = strip_cpp_ref_const;
    boxed_source = is_boxed_type;
    spells_as_any = Cpp_ir.Types.prints_as_any }

(** Whether [t] holds a type resolution has still to decide: an opaque one
    says nothing a coercion could act on. *)
let has_obligation = Cpp_ir.Types.exists (fun (t : Cpp_ir.Lowered.Type.t) -> match t with Obligation _ -> true | _ -> false)

(** [t] with its aliases unfolded and its spelling normalised: a type
    variable by the name C++ knows it under, an inductive without the
    namespace it is qualified by. *)
let normal al t =
  let rec spelled (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
    match t with
    | Variable (Index (_, Some n)) -> Variable (Named n)
    | Variable (Index (i, None)) -> Variable (Named (Cpp_ir.Type.positional_id i))
    | Const t | Reference (_, t) -> spelled t
    | In_namespace (g, (Entity_application (g', _, _) as t')) when GlobRef.CanOrd.equal g g' -> spelled t'
    | t -> t
  in
  let rec bare (t : Cpp_ir.Lowered.Type.t) = match t with Const t | Reference (_, t) -> bare t | t -> t in
  (* An alias may unfold to another alias, or to a qualified one. *)
  let rec unfolded n t =
    let t' = spelled (al.unfold (bare t)) in
    if n = 0 || t' = t then t' else unfolded (n - 1) t'
  in
  Cpp_ir.Types.map (unfolded 8) t

(** [a] with every leaf {!normal}: a closure's parameters as the values
    they take, whatever reference they are declared through. *)
let normal_arrows al (a : Cpp_ir.Lowered.Arrows.t) : Cpp_ir.Lowered.Arrows.t =
  let groups = List.map (List.map (normal al)) a.groups and result = normal al a.result in
  (* A result an alias spelled as a function continues the chain. *)
  match Cpp_ir.Arrows.of_type result with
  | Some r -> {groups = groups @ r.groups; result = r.result}
  | None -> {groups; result}

(** [decide_with aliases from into]: how a value of type [from] is adapted
    to a slot of type [into], or [None] where it fits as it is (typed CppIR
    design 3.3).  A total function of the two types; [aliases] only unfolds
    them.  The first row that matches answers. *)
let decide_with al (from : Cpp_ir.Lowered.Value_type.t) (into : Cpp_ir.Lowered.Slot_type.t) :
    Cpp_ir.Lowered.Coercion.plan option =
  let callable : Cpp_ir.Lowered.Value_type.t -> Cpp_ir.Lowered.Arrows.t option = function
    | Typed t -> Cpp_ir.Arrows.of_type (normal al t)
    | Closure a | Function_name (_, a) -> Some (normal_arrows al a)
    | Never | Deduced _ -> None
  in
  (* A generic lambda is a callable with no signature to read. *)
  let function_value = Option.has_some (callable from) || from = Deduced Generic_lambda in
  match (from, into) with
  | _, (Free | Forwarded | View _ | Join _ | Exactly Void) | Never, _ -> None
  | (Closure _ | Function_name _), Template_parameter t -> Some (Name t)
  | (Typed _ | Deduced _), Template_parameter _ -> None
  | _, Exactly into -> (
    let undecided = has_obligation into in
    let written = strip_cpp_ref_const into in
    let into = normal al into in
    let source = match from with Typed t -> Some (normal al t) | _ -> None in
    let classified =
      match source with
      | None -> `Unknown
      | Some f when al.boxed_source f -> `Boxed
      | Some f when Cpp_ir.Types.prints_as_any f -> `Opaque
      | Some f -> `Concrete f
    in
    (* Erased on both sides, a domain needs no adapter between them. *)
    let same_domain =
      match (callable from, Cpp_ir.Arrows.of_type into) with
      | Some {groups = d :: _; _}, Some {groups = d' :: _; _} ->
        List.compare_lengths d d' = 0
        && List.for_all2
             (fun a b -> cpp_ty_eq a b || a = b || (Cpp_ir.Types.prints_as_any a && Cpp_ir.Types.prints_as_any b))
             d d'
      | _ -> false
    in
    match (source, classified) with
    | Some t, _ when cpp_ty_eq t into || t = into -> None
    | _, `Boxed when al.spells_as_any written -> None
    (* A type an alias resolves to a box is a box only by that alias; one
       the slot leaves undecided is not read out of it. *)
    | Some t, `Boxed when undecided && not (is_boxed_type t) -> None
    | _, `Boxed -> (
      match Cpp_passes.Erasure.erased_list_shape into with
      | Some (g, shape) when Base.Table.is_custom g -> Some (Unbox (To shape))
      | Some (_, shape) -> Some (Unbox (List (into, shape)))
      | None -> Some (Unbox (To into)) )
    | _, `Opaque -> None
    | _ when is_boxed_type into || ((not undecided) && al.spells_as_any written) -> Some (Box (if function_value then Some Boxed_whole else None))
    | _ when function_value && erased_domain_fun_ty into -> (
      match into with Function (_, cod) -> Some (Erase (At_signature cod)) | _ -> None )
    | _ -> (
      match (callable from, Cpp_ir.Arrows.of_type into) with
      | Some a, Some b
        when Cpp_ir.Types.prints_as_any a.result
             && (not (has_obligation a.result))
             && not (Cpp_ir.Types.prints_as_any b.result) ->
        Some (Recover (a, b))
      (* A template's name is no value: one whose signature keeps a part
         only its instantiation decides is named through an adapter. *)
      | Some a, Some _ when (match from with Function_name _ -> has_obligation (Cpp_ir.Arrows.to_type a) | _ -> false) ->
        Option.map (fun b -> Cpp_ir.Coercion.Eta {declared = a; into = b}) (Cpp_ir.Arrows.of_type into)
      (* Nor is the name of a function taking a callable: such a parameter
         is a deduced [F&&], which makes the function a template
         ({!curry_value_to_expected}). *)
      | Some ({groups = d :: _; _} as a), Some b
        when (match from with Function_name _ -> true | _ -> false)
             && List.exists (fun t -> Option.has_some (Cpp_ir.Arrows.of_type (strip_cpp_ref_const t))) d ->
        Some (Eta {declared = a; into = b})
      | Some a, Some b when Cpp_ir.Arrows.equal a b || (same_domain && Cpp_ir.Arrows.same_function a b && List.length a.groups = List.length b.groups) -> None
      | Some a, Some b when Cpp_ir.Arrows.same_function a b -> (
        match from with
        | Function_name _ -> Some (Eta {declared = a; into = b})
        | _ -> Some (Regroup (a, b)) )
      | Some _, _ -> None
      | None, _ -> (
        match source with
        | Some t when has_obligation t || has_obligation into || Cpp_ir.Types.prints_as_any into -> None
        | Some t when Cpp_ir.Types.same_arrows t into -> Some (Convert into)
        | Some (Shared_pointer t) when cpp_ty_eq t into -> Some (Convert into)
        | Some t when (match into with Shared_pointer t' -> cpp_ty_eq t t' | _ -> false) -> Some (Convert into)
        (* A carrier reaching one at an erased element: converted element by
           element ({!convert_carrier_arg}). *)
        | Some (Apply (h, xs))
          when (match into with
                | Apply (h', ys) ->
                  h = h' && List.compare_lengths xs ys = 0 && List.exists Cpp_ir.Types.prints_as_any ys
                  && not (List.for_all Cpp_ir.Types.prints_as_any xs)
                | _ -> false) ->
          Some (Convert into)
        | Some _ | None -> None ) ) )

(** Whether C++ performs [p] on a value of type [from] by itself, so that
    a value left without it is still well-formed: a box of a value that is
    no callable (the box's converting constructor), and the erasure of a
    callable whose domain is erased already or which is generic (the
    [crane::fn] at the erased signature takes it as it is). *)
let implicit ?(al = as_written) (from : Cpp_ir.Lowered.Value_type.t) : Cpp_ir.Lowered.Coercion.plan -> bool = function
  | Box None -> true
  | Erase _ -> (
    match from with
    | Deduced Generic_lambda -> true
    | Typed t -> (
      match Cpp_ir.Arrows.of_type (normal al t) with
      | Some {groups = d :: _; _} -> List.for_all Cpp_ir.Types.prints_as_any d
      | _ -> false )
    | Closure {groups = d :: _; _} | Function_name (_, {groups = d :: _; _}) -> List.for_all Cpp_ir.Types.prints_as_any d
    | _ -> false )
  | _ -> false

(** {!decide_with} the aliases of the unit being lowered. *)
let decide cx from into = decide_with (aliases_in cx) from into

(** Whether [from] and the slot [into] are types no plan relates, where
    {!decide} finds no plan: neither a box nor opaque, and not one type, nor
    one callable grouped otherwise.  For diagnostics: such a pair is a type
    synthesised wrong, or a value C++ converts by itself. *)
let unrelated cx (from : Cpp_ir.Lowered.Value_type.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  let al = aliases_in cx in
  let undecided t = has_obligation t || Cpp_ir.Types.prints_as_any t || al.boxed_source t in
  (* Equal where both decide: an erased or undecided part on either side
     says nothing the other could contradict. *)
  let rec agree (a : Cpp_ir.Lowered.Type.t) (b : Cpp_ir.Lowered.Type.t) =
    undecided a || undecided b || cpp_ty_eq a b || a = b
    ||
    match (a, b) with
    | Entity_application (g, xs, _), Entity_application (g', ys, _) -> GlobRef.CanOrd.equal g g' && all xs ys
    | Named (x, xs), Named (y, ys) -> Id.equal x y && all xs ys
    | External (x, xs), External (y, ys) -> String.equal x y && all xs ys
    | Function (d, c), Function (d', c') -> all d d' && agree c c'
    | Shared_pointer a, Shared_pointer b | Pointer a, Pointer b -> agree a b
    | Variant (k, xs), Variant (k', ys) -> k = k' && all xs ys
    | Foreign f, Foreign f' -> GlobRef.CanOrd.equal f.custom f'.custom && all f.types f'.types
    | Apply (f, xs), Apply (g, ys) -> agree f g && all xs ys
    | _ -> false
  and all xs ys = List.compare_lengths xs ys = 0 && List.for_all2 agree xs ys in
  let curried_agree a b =
    let (d, r) = Cpp_ir.Arrows.curried a and (d', r') = Cpp_ir.Arrows.curried b in
    all d d' && agree r r'
  in
  match (from, into) with
  | Typed t, Exactly t' ->
    let t = normal al t and t' = normal al t' in
    t' <> Void && not (agree t t')
  | (Closure a | Function_name (_, a)), Exactly t' -> (
    match Cpp_ir.Arrows.of_type (normal al t') with
    | Some b -> not (curried_agree (normal_arrows al a) b)
    | None -> not (undecided (normal al t')) )
  | _ -> false

(** Under [CRANE_PROBE], the boundary shadow check: [after], what the
    adapter named [adapter] built from [before] for a slot of type [into],
    held to what {!decide} plans for a value of type [from] there.  An
    adapter that built nothing is not compared: its caller may adapt the
    value otherwise. *)
let shadow ?(al = as_written) ~adapter ~kind (from : Cpp_ir.Lowered.Value_type.t) (into : Cpp_ir.Lowered.Slot_type.t)
    ~(before : Cpp_ir.Lowered.Expr.t) (after : Cpp_ir.Lowered.Expr.t) =
  (* The other direction, counted: an adapter that built nothing where
     {!decide} plans a coercion C++ does not perform by itself, at a slot
     both sides can be compared at. *)
  if Base.Probe.enabled () && (after == before || after = before) then begin
    match (decide_with al from into, into) with
    | Some p, Exactly t
      when (not (implicit ~al from p))
           && (not (Cpp_ir.Value_type.not_yet_typed from))
           && (not (contains_tvar t))
           && not (Cpp_ir.Types.exists (fun t -> t = Auto) t) ->
      Base.Probe.hit "typed-declined" (fun () ->
          adapter ^ " " ^ Cpp_ir.Coercion.plan_name p ^ " in " ^ Base.Probe.library () ^ " from "
          ^ Binders.show_value_type from ^ " into " ^ Binders.type_shape t )
    | _ -> Base.Probe.hit "typed-declined" (fun () -> adapter ^ " none")
  end;
  (* An adapter may rebuild what it was given unchanged. *)
  if (Base.Probe.enabled () || Base.Probe.checking ()) && after != before && after <> before then begin
    let planned = Option.map Cpp_ir.Coercion.plan_name (decide_with al from into) in
    let agrees = match planned with Some p -> List.mem p kind | None -> List.mem "none" kind in
    let variables = function
      | Cpp_ir.Grammar.Slot_type.Exactly t -> contains_tvar t
      | _ -> false
    in
    let verdict =
        if agrees then " agree"
        else if into = Free then " unchecked (no slot type)"
        else if Cpp_ir.Value_type.not_yet_typed from then " unchecked (untyped value)"
        else if (match into with Exactly t -> Cpp_ir.Types.exists (fun t -> t = Auto) t | _ -> false) then
          " unchecked (generic slot)"
        else if planned = None && variables into then " unchecked (slot at type variables)"
        else if
          (* A callable said to fill a slot no callable fills: the position
             described the aggregate the value goes into, not the value's
             own slot (typed CppIR B1 gives every position its slot). *)
          planned = None
          && Option.has_some (Cpp_ir.Value_type.arrows from)
          && match into with
             | Exactly t ->
               let t = normal al t in
               Cpp_ir.Arrows.of_type t = None && not (al.boxed_source t || al.spells_as_any t)
             | _ -> false
        then " unchecked (slot is no callable's)"
        else
          " disagree decide " ^ Option.default "none" planned ^ " in " ^ Base.Probe.library () ^ " built " ^ String.concat "/" kind ^ " from "
          ^ Binders.show_value_type from ^ " into "
          ^ match into with Exactly t -> Binders.type_shape t | _ -> "?"
    in
    Base.Probe.hit "typed-shadow" (fun () -> adapter ^ verdict);
    if String.starts_with ~prefix:" disagree" verdict then
      Base.Probe.violation "coercion shadow" Pp.(str adapter ++ str verdict)
  end;
  after

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
let name_fn_arg_built param_core_ty (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match (resolve_meta param_core_ty, expr) with
  | Core.Type.Variable _, Lambda _ -> Function_value expr
  | _ -> expr

(** [regroup_value ~from ~into expr]: [expr], a function value of the C++
    type [from], as one of [into] where the two are one function type with
    its arrows grouped otherwise ({!Cpp_ir.Types.same_arrows}) and [into]
    takes at least as many arguments at once as [from] at every step -- a
    curried value reaching a flat slot: an adapter taking [into]'s
    arguments and applying [expr] to them as [from] groups them,
    [\[=\](A a, B b) { return f(a)(b); }].  The other direction, a flat value
    reaching a curried slot, is the curried adapter of
    {!curry_value_to_expected}.  [expr] itself where the types are not so
    related. *)
let regroup_value_built ~(from : Cpp_ir.Lowered.Type.t) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let rec go depth (from : Cpp_ir.Lowered.Type.t) (into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) =
    let from = strip_cpp_ref_const from and into = strip_cpp_ref_const into in
    match (from, into) with
    | Function _, Function (dom', cod') when from <> into && Cpp_ir.Types.same_arrows from into -> (
      let params = adapter_params ~prefix:(Printf.sprintf "_rg%d_" depth) dom' in
      (* [f] applied to [args] group by group as its type [t] takes them;
         [None] where a group would straddle the end of [args]. *)
      let rec apply f (t : Cpp_ir.Lowered.Type.t) args =
        match (strip_cpp_ref_const t, args) with
        | t, [] -> Some (f, t)
        | Function (d, c), _ when List.compare_length_with args (List.length d) >= 0 ->
          let now = List.filteri (fun i _ -> i < List.length d) args
          and rest = List.filteri (fun i _ -> i >= List.length d) args in
          apply (Cpp_ir.Build.call f now) c rest
        | _ -> None
      in
      match apply expr from (List.map adapter_arg params) with
      | Some (body, rest) ->
        Cpp_ir.Build.lambda params None [Return (Some (go (depth + 1) rest cod' body))] ~capture:Stored
      | None -> expr )
    | _ -> expr
  in
  go 0 from into expr

(** [grouped_lambda ?into params body]: a closure taking [params] and
    returning [body], its parameters grouped as the function type [into]
    groups its arrows -- [\[=\](A a) { return \[=\](B b) { return body; }; }]
    for a curried [into] -- where [into]'s domains are [params]' types,
    group by group; one flat closure otherwise.  A closure built to fill a slot (a
    partial application's) takes its arguments as the slot hands them. *)
let grouped_lambda ?(into : Cpp_ir.Lowered.Type.t option) params (body : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let flat () = Cpp_ir.Build.lambda params None [Return (Some body)] ~capture:Stored in
  let same (a : Cpp_ir.Lowered.Type.t) (b : Cpp_ir.Lowered.Type.t) = strip_cpp_ref_const a = strip_cpp_ref_const b in
  (* The group sizes, where [t]'s domains are [params]' types in order. *)
  let rec groups (t : Cpp_ir.Lowered.Type.t) (ps : Cpp_ir.Lowered.Type.t list) =
    if ps = [] then Some []
    else
      match strip_cpp_ref_const t with
      | Function (d, c) when List.compare_lengths d ps <= 0 ->
        let now = List.filteri (fun i _ -> i < List.length d) ps
        and rest = List.filteri (fun i _ -> i >= List.length d) ps in
        if List.for_all2 same d now then Option.map (fun gs -> List.length d :: gs) (groups c rest) else None
      | _ -> None
  in
  match Option.map strip_cpp_ref_const into with
  | Some (Function _ as t) -> (
    match groups t (List.map fst params) with
    | Some (_ :: _ :: _ as gs) ->
      let rec build ps = function
        | [] -> body
        | g :: gs ->
          let now = List.filteri (fun i _ -> i < g) ps and rest = List.filteri (fun i _ -> i >= g) ps in
          Cpp_ir.Build.lambda now None [Return (Some (build rest gs))] ~capture:Stored
      in
      build params gs
    | _ -> flat () )
  | _ -> flat ()

(** Apply a callee recovered from a bare [std::any], one argument at a time.

    Nothing about a boxed callable says how many arguments it takes: the
    producer's lambda stops at the first codomain that erases, so a value of an
    opaque function type ([nfun 2], a type-level [Fixpoint]) is a chain of unary
    [std::function<std::any(std::any)>]s.  Handing it every argument at once
    would cast it to a signature it was never stored at. *)
let apply_erased_curried ?(box = false) (callee : Cpp_ir.Lowered.Expr.t) arg_exprs : Cpp_ir.Lowered.Expr.t =
  List.fold_left
    (fun (f : Cpp_ir.Lowered.Expr.t) a ->
      let a = if box then Cpp_passes.Erasure.converting_ctor Any [a] else a in
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
let eta_expand_built ?(expected_ty : Cpp_ir.Lowered.Type.t option) ~core_arity ~returns_a_lambda ~arity
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
    [shared_ptr]) is delegated to {!Convert.gen_type_conversion_expr}, which already
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
let rec coerce_built cx ?term ?(from : Cpp_ir.Lowered.Type.t option) ~(into : Cpp_ir.Lowered.Type.t)
  (expr : Cpp_ir.Lowered.Expr.t) :
    Cpp_ir.Lowered.Expr.t =
  let source = Erasure.classify_erasure cx from in
  let same_type = match from with Some f -> cpp_ty_eq f into | None -> false in
  if same_type || into = Void then expr
  else
    match source with
    (* Casting a box to a name that is itself the box is not a recovery but
       an [any_cast<std::any>], which only succeeds on a doubly-boxed value
       and otherwise throws. *)
    | `Boxed when Erasure.spells_as_any cx into -> expr
    (* A closure built here is not a box, whatever its erased type says: what
       is boxed is what it returns -- [@id lit] eta-expanded, with [id : ID]
       erased to [std::any id(std::any)], read at [Endo<lit>].  Its returns
       are recovered at the codomain instead. *)
    | `Boxed when (match expr with Lambda _ -> true | _ -> false) -> (
      match (expr, Types.unfold_cpp_typedef cx (empty_env ()) into) with
      | Lambda l, Function (_, cod) ->
        let rec at_returns : Cpp_ir.Lowered.Stmt.t -> Cpp_ir.Lowered.Stmt.t = function
          | Return (Some e) -> Return (Some (coerce_built cx ~from:Any ~into:cod e))
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
        match Cpp_passes.Erasure.erased_list_shape into with
        (* A custom list has no converting constructor to unbox its elements
           with, so it stays at the flat shape until a consumer converts it. *)
        | Some (g, shape) when Base.Table.is_custom g -> Cpp_passes.Erasure.unbox shape expr
        | Some (_, shape) -> Cpp_passes.Erasure.converting_ctor into [Cpp_passes.Erasure.unbox shape expr]
        | None -> Cpp_passes.Erasure.unbox into expr ) )
    (* Nothing may be boxed or cast on the strength of an admission that the
       representation is unknown. *)
    | `Opaque -> expr
    | (`Unknown | `Concrete _) as concrete_source -> (
      let is_function_value =
        match concrete_source with
        | `Concrete (Function _) -> true
        | `Concrete _ -> false
        | `Unknown -> ( match term with Some t -> Erasure.core_expr_is_function_value cx t | None -> false )
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
          Cpp_passes.Erasure.converting_ctor Any [adapted]
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
                coerce_built cx ~from:ty ~into (adapter_arg p) )
              params
          in
          let call = coerce_built cx ~from:scod ~into:cod (Cpp_ir.Build.call expr args) in
          Cpp_ir.Build.lambda params None [Return (Some call)] ~capture:Stored
        | _ -> (
          match concrete_source with
          | `Concrete f when not (Cpp_ir.Types.prints_as_any into) ->
            Convert.gen_type_conversion_expr ~src_ty:f ~dst_ty:into expr
          | _ -> expr ) )

(** The kind of adapter [e] is, as {!coerce} builds them, named as the
    plan {!decide} would name it. *)
let coerced_kind : Cpp_ir.Lowered.Expr.t -> string = function
  | Box _ | Converting_construct (Any, _) -> "box"
  | Erase_callable _ -> "erase"
  | Unbox _ | Any_cast _ | Converting_construct (_, [(Unbox _ | Any_cast _)]) -> "unbox"
  | Lambda _ -> "recover"
  | Convert _ -> "convert"
  | Container_cast _ -> "container cast"
  | _ -> "other"

(** [regroup_crossing ~from ~into expr]: [expr], whose C++ type is [from],
    read at [into] where the two differ only in how their arrows are grouped
    ({!Cpp_ir.Types.arrow_site}) -- a value spelled where it was declared reaching
    a slot a type argument spells curried, or back.  [crane_convert] regroups
    every function the value holds ([crane_cast_to] for [crane::fn] of
    another arity).  A function value itself is not this: it reaches a slot
    through the adapter {!curry_value_to_expected} writes,
    whose type is the slot's. *)
let regroup_crossing_built ~(from : Cpp_ir.Lowered.Type.t) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) :
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
    ({!Binders.planned_binder_type_or_derive}). *)
let value_cpp_type cx ~agree env e =
  match strip_magic e with
  | Core.Expr.Bound_variable {index = j; occurrence = occ} ->
    Binders.planned_binder_type_or_derive cx ~use:"value's type" ~agree env j occ
  | Core.Expr.Global ({callee = r; _} as use) when Base.Core_util.Var_types.is_empty (Base.Core_util.written_type_args use) ->
    Option.map (Types.cpp_of_core cx env) (callee_core_type cx r)
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

    The mirror is {!Functions.dead_unit_returns_to_abort}, which catches the
    same branch where extraction recorded no coercion at all and a bare [tt]
    reaches a [return]; both throw {!Cpp_build.dead_branch_message}. *)
let absurd_coercion cx from (into : Cpp_ir.Lowered.Type.t) =
  Base.Type_util.core_type_is_unit from
  && (not (is_cpp_unit_type into))
  && into <> Void
  && not (Types.resolves_to_any_type cx into)

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
          Cpp_passes.Erasure.erased_list_shape (Types.cpp_of_core cx (empty_env ()) t) )
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
  | _ when Erasure.core_expr_is_function_value cx e -> wrap_crane_erase_fn Boxed_whole expr
  | _ -> ( match kind with Family_box -> deep_box_list cx e expr | Var_box -> expr )


(** [stored_adapter params e]: the lambda taking [params], in source order,
    that returns [e] and holds its captures by copy, its return type
    deduced. *)
let stored_adapter ?(moved = []) params (e : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  Lambda
    { params;
      type_params = [];
      return_type = None;
      body = [Return (Some e)];
      capture = Stored;
      moved;
      binders = [];
      modes = [];
      fixpoint = None }

(** Whether a parameter of type [ty] an adapter takes is worth moving into
    a closure capture rather than copying: one it owns, by value, whose copy
    costs something ({!Ownership_ir.Region.worth_moving_cpp}).  A reference
    ([auto &&] may name the caller's lvalue) and a [const] value are
    copied. *)
let adapter_param_moves (ty : Cpp_ir.Lowered.Type.t) =
  match ty with
  | Reference _ | Const _ -> false
  | _ -> Ownership_ir.Region.worth_moving_cpp ty

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
let curry_value_to_expected_built cx env ?(expected_ty : Cpp_ir.Lowered.Type.t option) ?(callee_site = Cpp_ir.Types.Declared)
  ?(exact = false) core_ty
    (cglob : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let decl_dom, decl_cod =
    match Option.map (Types.cpp_of_core cx env) core_ty with
    | Some (Function (dom, cod)) -> (dom, Some cod)
    | _ -> ([], None)
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
    (* Where the slot is declared at a type variable -- a parameter of
       [fold_left]'s step, [A -> B -> A] -- what the declaration takes or
       returns at a function type passes through that variable, which spells
       it curried ({!Cpp_ir.Types.spell_arrows}): the adapter takes such a
       parameter curried and hands the callee a flat closure applying it one
       argument at a time, and returns curried what follows. *)
    let exp_dom, exp_cod =
      let rec strip (t : Cpp_ir.Lowered.Type.t) = match t with Const t | Reference (_, t) -> strip t | t -> t in
      match Option.map strip expected_ty with
      | Some (Function (dom, cod)) -> (List.map strip dom, Some (strip cod))
      | _ -> ([], None)
    in
    let through_variable i =
      match List.nth_opt exp_dom i with Some (Cpp_ir.Type.Variable _) -> true | _ -> false
    in
    let curried (ty : Cpp_ir.Lowered.Type.t) = Cpp_ir.Types.spell_arrows Through_tvar ty in
    let decl_dom =
      List.mapi
        (fun i (ty : Cpp_ir.Lowered.Type.t) ->
          match ty with Function (_ :: _ :: _, _) when through_variable i -> curried ty | ty -> ty )
        decl_dom
    in
    let params = adapter_params ~prefix:"_ec" decl_dom in
    let passed i ((ty : Cpp_ir.Lowered.Type.t), id) : Cpp_ir.Lowered.Expr.t =
      match (List.nth_opt exp_dom i, ty) with
      | Some (Variable _), Function ([_], Function _) -> (
        (* The flat signature the curried parameter stands for. *)
        let rec flat (t : Cpp_ir.Lowered.Type.t) =
          match t with
          | Function ([a], (Function _ as c)) -> (
            match flat c with Cpp_ir.Type.Function (d, r) -> Cpp_ir.Type.Function (a :: d, r) | r -> r )
          | t -> t
        in
        match flat ty with
        | Function (dom, _) ->
          let ps = adapter_params ~prefix:(Id.to_string (Option.get id) ^ "_") dom in
          stored_adapter ps
            (Cpp_ir.Typed.apply
               (Cpp_ir.Typed.typed ty (Local (Option.get id)))
               (List.map (fun p -> Cpp_ir.Typed.of_node (adapter_arg p)) ps) )
              .expr
        | _ -> adapter_arg (ty, id) )
      | _ -> adapter_arg (ty, id)
    in
    (* The callee takes the parameters as the site it is spelled at groups
       them. *)
    let call =
      let callee_ty = Cpp_ir.Types.spell_arrows callee_site (Function (decl_dom, Option.default Cpp_ir.Type.Auto decl_cod)) in
      (Cpp_ir.Typed.apply (Cpp_ir.Typed.typed callee_ty cglob) (List.mapi (fun i p -> Cpp_ir.Typed.of_node (passed i p)) params))
        .expr
    in
    let expected_ty =
      match (expected_ty, exp_cod, decl_cod) with
      | Some _, Some (Variable _), Some cod when List.length decl_dom > List.length exp_dom ->
        let rest = List.filteri (fun i _ -> i >= List.length exp_dom) decl_dom in
        Some (Cpp_ir.Type.Function (exp_dom, curried (Function (rest, cod))))
      | _ -> expected_ty
    in
    (* One lambda per group of arguments the slot takes at a time, as deep as
       it nests: [fn<fn<fn<R(C)>(B)>(A)>] takes [A], then [B], then [C].  A
       group's lambda does nothing but return the next one, so the next one
       takes the parameters it owns by move ({!adapter_param_moves}); deeper
       lambdas copy them, out of a capture they cannot move from. *)
    let rec nest ~moved params (expected : Cpp_ir.Lowered.Type.t option) =
      match expected with
      | Some (Const t | Reference (_, t)) -> nest ~moved params (Some t)
      | Some (Function (dom, cod)) when dom <> [] && List.length params > List.length dom ->
        let k = List.length dom in
        let outer = List.filteri (fun i _ -> i < k) params in
        let owned = List.filter_map (fun (ty, id) -> if adapter_param_moves ty then id else None) outer in
        stored_adapter ~moved outer (nest ~moved:owned (List.filteri (fun i _ -> i >= k) params) (Some cod))
      | _ -> stored_adapter ~moved params call
    in
    nest ~moved:[] params (if n_outer < List.length params then expected_ty else None)

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
         && (not (Erasure.core_expr_is_function_value cx e))
         && (match param_cpp_ty with Function _ -> false | _ -> true) ->
    Cpp_ir.Expr.Convert (param_cpp_ty, expr)
  | _ -> expr

(** [erase_fn_arg_for_param env param_ty e expr] wraps a function-valued
    argument when the callee's parameter type is the canonical erased
    [std::function<std::any(std::any...)>] adapter (e.g. a class method
    polymorphic in its own type argument, [forall A, (A -> A) -> A -> A]):
    a concrete closure does not convert to the erased signature. *)
let erased_param cx env param_core_ty =
  let open Cpp_ir.Expr.Erase_shape in
  (* The callee has already written this parameter down, so any opaque type in
     it has been spelled [std::any] in the header and the slot really is
     boxed. *)
  let param_cpp_ty = materialise_opaque (Types.cpp_of_core cx env param_core_ty) in
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
    | ty when Types.resolves_to_any_type cx ty -> Some Boxed_whole
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
          Erasure.value_indexed_family r || List.exists mentions_family args
        | Core.Type.Arrow {parameter = a; result = b} -> mentions_family a || mentions_family b
        | Core.Type.Variable_app {arguments = args; _} -> List.exists mentions_family args
        | _ -> false
      in
      match expand_core_fun_alias param_core_ty with
      | Core.Type.Arrow _ as t
        when List.exists mentions_family (core_domains t) ->
        let cod = core_codomain t in
        if mentions_family cod then Some (At_signature Any)
        else Some (At_signature (Types.cpp_of_core cx env cod))
      | _ -> None )
  in
  (param_cpp_ty, erased_fn_param)

(** [erase_fn_arg_built env param_ty e expr]: the argument [e], lowered as
    [expr], adapted to the parameter the callee declared at [param_ty]
    ({!erased_param}): a callable through [crane_erase_fn] where the
    parameter is erased, a carrier converted ({!convert_carrier_arg}). *)
let erase_fn_arg_built cx env param_core_ty e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let param_cpp_ty, erased_fn_param = erased_param cx env param_core_ty in
  match erased_fn_param with
  | Some shape when Erasure.core_expr_is_function_value cx e -> Cpp_ir.Expr.Erase_callable (shape, expr)
  | _ -> convert_carrier_arg cx param_core_ty param_cpp_ty e expr

(** A mapping's text takes each argument as it comes, deducing [auto] from
    it: a callable handed for a parameter declared at a type variable is the
    type of whatever the text keeps it in -- a fold's accumulator, assigned
    each step's result, a different closure.  So it arrives named: at the
    instantiation [spelled] where this scope can spell it (a closure
    returning a closure deduced through [crane::fn] would have the inner
    closure's own type as its result, which no later step's result is),
    else at the [crane::fn] it deduces ({!Cpp_ir.Expr.Function_value}). *)
let mapping_name_built (spelled : Cpp_ir.Lowered.Type.t option) (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  match (expr, spelled) with
  | Function_value _, _ -> expr
  | _, Some f -> Converting_construct (f, [expr])
  | _, None -> Function_value expr

(** The adapters of section 0 of the typed CppIR design that go through
    {!into_slot}, each by the name its parameters are prefixed with (B1's
    origin tag), carrying what its expansion reads beyond the value and
    the slot. *)
type origin =
  | Rg  (** {!regroup_value}: [_rg] *)
  | Ee of {core_arity : int; returns_a_lambda : bool; arity : int}  (** {!eta_expand_to_expected}: [_ee] *)
  | Ec of {
      cx : Lowering_state.t;
      env : env;
      core_ty : Core.Type.t option;
      callee_site : Cpp_ir.Types.arrow_site option;
      exact : bool option;
    }  (** {!curry_value_to_expected}: [_ec] *)
  | Crossing  (** {!regroup_crossing}: [crane_convert] *)
  | Tvar_name of Core.Type.t  (** {!name_fn_arg_for_tvar_param}: [crane::fn] *)
  | Ue of {
      cx : Lowering_state.t;
      term : Core.Expr.t option;
      from : Cpp_ir.Lowered.Type.t option;
    }  (** {!coerce}: box, unbox, erase, recover ([_ue]), convert *)
  | Param of {
      cx : Lowering_state.t;
      env : env;
      param_core_ty : Core.Type.t;
      term : Core.Expr.t;
    }  (** {!erase_fn_arg_for_param}: erase a callable, convert a carrier *)
  | Mapping_name
      (** {!mapping_name_built}: a callable at an inline mapping's parameter
          declared at a type variable, named *)
  | Pa
      (** {!grouped_lambda}: the closure a partial application leaves
          ({!Cpp_ir.Typed.apply}), regrouped by nesting its own
          parameters rather than wrapped *)

(** The adapter an origin names, for the census. *)
let origin_name = function
  | Rg -> "regroup_value"
  | Ee _ -> "eta_expand_to_expected"
  | Ec _ -> "curry_value_to_expected"
  | Crossing -> "regroup_crossing"
  | Tvar_name _ -> "name_fn_arg_for_tvar_param"
  | Ue _ -> "coerce"
  | Param _ -> "erase_fn_arg_for_param"
  | Pa -> "grouped_lambda"
  | Mapping_name -> "mapping_name"

(** The plans an origin's expansion builds, by {!Cpp_ir.Coercion.plan_name}. *)
let builds = function
  | Rg | Ee _ | Pa -> ["regroup"]
  | Ec _ -> ["eta"; "regroup"]
  | Crossing -> ["convert"]
  | Tvar_name _ | Mapping_name -> ["name"]
  | Ue _ -> ["box"; "deep box"; "unbox"; "erase"; "recover"; "convert"; "container cast"]
  | Param _ -> ["erase"; "box"; "convert"]

(** Whether {!decide} answers for a value of type [from] at [into]: a typed
    value and a slot that states a type, neither mentioning a type variable
    (the two may number them differently), the slot no generic one, and not
    a callable said to fill a slot no callable fills (a position describing
    the aggregate the value goes into).  Where it does not, the adapter's
    own test still decides; phase C removes those. *)
let decides al (from : Cpp_ir.Lowered.Value_type.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  match into with
  | Exactly t ->
    (not (Cpp_ir.Value_type.not_yet_typed from))
    && (not (contains_tvar t))
    && (not (Cpp_ir.Types.exists (fun t -> t = Auto) t))
    && (match from with
        | Typed f -> not (contains_tvar f)
        | Closure a | Function_name (_, a) -> not (contains_tvar (Cpp_ir.Arrows.to_type a))
        | _ -> true)
    &&
    let t = normal al t in
    not
      (Option.has_some (Cpp_ir.Value_type.arrows from)
       && Cpp_ir.Arrows.of_type t = None
       && not (al.boxed_source t || al.spells_as_any t))
  | _ -> false

(** The adapter body an origin names, applied to [x] for the slot [into]. *)
let expand origin (x : Cpp_ir.Typed.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  let stated = match into with Exactly t -> Some t | _ -> None in
  match (origin, x.ty, stated) with
  | Rg, Typed from, Some into -> regroup_value_built ~from ~into x.expr
  | Crossing, Typed from, Some into -> regroup_crossing_built ~from ~into x.expr
  | Ee {core_arity; returns_a_lambda; arity}, _, expected_ty ->
    eta_expand_built ?expected_ty ~core_arity ~returns_a_lambda ~arity x.expr
  | Ec {cx; env; core_ty; callee_site; exact}, _, expected_ty ->
    curry_value_to_expected_built cx env ?expected_ty ?callee_site ?exact core_ty x.expr
  | Tvar_name t, _, _ -> name_fn_arg_built t x.expr
  | Ue {cx; term; from}, _, Some into -> coerce_built cx ?term ?from ~into x.expr
  | Ue _, _, None -> x.expr
  | Param {cx; env; param_core_ty; term}, _, _ -> erase_fn_arg_built cx env param_core_ty term x.expr
  | Mapping_name, _, _ -> (
    match into with Template_parameter spelled -> mapping_name_built spelled x.expr | _ -> x.expr )
  | Pa, _, into -> (
    match x.expr with
    | Lambda {params; body = [Return (Some body)]; _} -> grouped_lambda ?into params body
    | e -> e )
  | (Rg | Crossing), _, _ -> x.expr

(** [into_slot ~origin x into]: [x] put in the slot [into] through the
    adapter [origin] names.  Where {!decide} answers ({!decides}), its plan
    decides whether the adapter is built at all; elsewhere the adapter's own
    test does.  Held to {!decide} under [CRANE_PROBE] ({!shadow}). *)
let into_slot ?(al = as_written) ~origin (x : Cpp_ir.Typed.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  (* [std::any] built from what is a [std::any] already, once aliases are
     followed, is the box itself (C++'s converting constructor excludes the
     box's own type): an identity {!coerce} still spells, kept until phase
     C so that output does not change. *)
  let box_of_box =
    match (origin, x.ty) with
    | Ue _, Typed t -> al.spells_as_any (normal al t) || Cpp_ir.Types.prints_as_any (normal al t)
    | _ -> false
  in
  let built =
    if decides al x.ty into && not box_of_box then
      match decide_with al x.ty into with
      | Some p when List.mem (Cpp_ir.Coercion.plan_name p) (builds origin) -> expand origin x into
      | _ -> x.expr
    else expand origin x into
  in
  (* What was built, named as the plan {!decide} would name it. *)
  let kind =
    match origin with
    | Ue _ -> ( match coerced_kind built with "box" when box_of_box -> ["box"; "none"] | k -> [k] )
    | Param _ -> (
      match built with
      | Erase_callable (Boxed_whole, _) -> ["box"]
      | Erase_callable _ -> ["erase"]
      | Convert _ -> ["convert"]
      | _ -> ["other"] )
    (* A value already of a nameable type, or one only C++ knows the type
       of, is named all the same: the text keeps it in an [auto], and the
       copy is an identity C++ performs, kept until phase C so that output
       does not change. *)
    | Mapping_name -> ( match x.ty with Typed _ | Deduced _ -> ["name"; "none"] | _ -> builds origin )
    | _ -> builds origin
  in
  shadow ~al ~adapter:(origin_name origin) ~kind x.ty into ~before:x.expr built

let slot_of_expected (t : Cpp_ir.Lowered.Type.t option) : Cpp_ir.Lowered.Slot_type.t =
  match t with Some t -> Exactly t | None -> Free

(** {!name_fn_arg_built} through {!into_slot}. *)
let name_fn_arg_for_tvar_param param_core_ty (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  into_slot ~origin:(Tvar_name param_core_ty) (Cpp_ir.Typed.of_node expr) (Template_parameter None)

(** {!regroup_value_built} through {!into_slot}. *)
let regroup_value ~(from : Cpp_ir.Lowered.Type.t) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) =
  into_slot ~origin:Rg (Cpp_ir.Typed.typed from expr) (Exactly into)

(** {!eta_expand_built} through {!into_slot}. *)
let eta_expand_to_expected ?(expected_ty : Cpp_ir.Lowered.Type.t option) ~core_arity ~returns_a_lambda ~arity
    (f : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  into_slot ~origin:(Ee {core_arity; returns_a_lambda; arity}) (Cpp_ir.Typed.of_node f) (slot_of_expected expected_ty)

(** {!regroup_crossing_built} through {!into_slot}. *)
let regroup_crossing ~(from : Cpp_ir.Lowered.Type.t) ~(into : Cpp_ir.Lowered.Type.t) (expr : Cpp_ir.Lowered.Expr.t) =
  into_slot ~origin:Crossing (Cpp_ir.Typed.typed from expr) (Exactly into)

(** {!curry_value_to_expected_built} through {!into_slot}: a global's name
    is taken at the grouping it is declared at, a variable at its type. *)
let curry_value_to_expected cx env ?(expected_ty : Cpp_ir.Lowered.Type.t option) ?callee_site ?exact core_ty
    (cglob : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  let declared = Option.map (Types.cpp_of_core cx env) core_ty in
  let from : Cpp_ir.Lowered.Value_type.t =
    match (cglob, declared) with
    | Entity (r, _, _), Some (Function (dom, cod)) -> (
      match Cpp_ir.Arrows.of_type (Function (dom, Cpp_ir.Types.spell_arrows Through_tvar cod)) with
      | Some a -> Function_name (r, a)
      | None -> Typed (Function (dom, cod)) )
    | _, Some t -> Typed t
    | _, None -> Deduced Not_yet_typed
  in
  into_slot ~al:(aliases_in cx) ~origin:(Ec {cx; env; core_ty; callee_site; exact}) (Cpp_ir.Typed.v ~ty:from cglob)
    (slot_of_expected expected_ty)

(** {!coerce_built} through {!into_slot}. *)
let coerce cx ?term ?(from : Cpp_ir.Lowered.Type.t option) ~(into : Cpp_ir.Lowered.Type.t)
    (expr : Cpp_ir.Lowered.Expr.t) =
  (* A lambda is a closure, whatever box the caller says it comes from. *)
  let from_ty : Cpp_ir.Lowered.Value_type.t =
    match (from, expr) with
    | _, Lambda _ | None, _ -> Cpp_ir.Typed.node_type expr
    | Some t, _ -> Typed t
  in
  into_slot ~al:(aliases_in cx) ~origin:(Ue {cx; term; from}) (Cpp_ir.Typed.v ~ty:from_ty expr) (Exactly into)

(** [recover_boxed_component into e] opens the box when [e] is evidently a
    component read out of a pair that was recovered from one.  The context's
    type [into] is what the value is declared to be; the emitted expression is
    the evidence that it is physically a [std::any]. *)
let recover_boxed_component cx into (e : Cpp_ir.Lowered.Expr.t) =
  if Erasure.yields_boxed_component e then coerce cx ~from:Any ~into e else e

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

(** {!erase_fn_arg_built} through {!into_slot}: the argument [e] lowered
    as [expr], at the parameter the callee declares at [param_core_ty]. *)
let erase_fn_arg_for_param cx env param_core_ty e (expr : Cpp_ir.Lowered.Expr.t) : Cpp_ir.Lowered.Expr.t =
  (* The parameter as the callee declares it: erased where only the Core
     type says so, a value-indexed family the C++ type in this scope does
     not show ([fn(Inst::sem)->bool], [sem] erased in the functor's
     body). *)
  let slot : Cpp_ir.Lowered.Slot_type.t =
    match erased_param cx env param_core_ty with
    | Function (dom, _), Some (At_signature cod) -> Exactly (Function (List.map (fun _ -> Cpp_ir.Type.Any) dom, cod))
    | _, Some Boxed_whole -> Exactly Any
    | t, _ -> Exactly t
    | exception e when CErrors.noncritical e -> Free
  in
  into_slot ~al:(aliases_in cx) ~origin:(Param {cx; env; param_core_ty; term = e}) (Cpp_ir.Typed.of_node expr) slot
