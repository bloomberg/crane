(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The checks typed lowering is held to while the types it synthesises
    run alongside the expressions they type (typed CppIR phase A): a census
    of what each Core form is typed as, under [CRANE_PROBE]. *)

module Typed = Cpp_ir.Typed

(** The name of [e]'s form, for the census. *)
let form_name : Core.Expr.t -> string = function
  | Bound_variable _ -> "variable"
  | Apply _ -> "apply"
  | Lambda _ -> "lambda"
  | Let _ -> "let"
  | Global _ -> "global"
  | Construct _ -> "construct"
  | Tuple _ -> "tuple"
  | Match _ -> "match"
  | Fixpoint _ -> "fixpoint"
  | Cofixpoint _ -> "cofixpoint"
  | Runtime_error _ -> "runtime-error"
  | Erased_value _ -> "erased"
  | Axiom_value _ -> "axiom"
  | Coerce _ -> "coerce"
  | Boxed_value _ -> "boxed"
  | Lambda_group_barrier _ -> "barrier"
  | UInt63 _ -> "uint63"
  | Float64 _ -> "float64"
  | String _ -> "string"
  | Persistent_array _ -> "array"
  | Numeral _ -> "numeral"

(** The kind of a value type, for the census. *)
let kind_name : Cpp_ir.Lowered.Value_type.t -> string = function
  | Typed _ -> "typed"
  | Closure _ -> "closure"
  | Function_name _ -> "function-name"
  | Never -> "never"
  | Deduced d -> "deduced:" ^ String.map (function ' ' -> '-' | c -> c) (Cpp_ir.Value_type.deduction_name d)


(** [adapted_to t e]: [e], an adapter built to fill a slot of type [t], at
    that type: a closure grouped as [t] where [t] is a function type. *)
let adapted_to (t : Cpp_ir.Lowered.Type.t option) e =
  match Option.map Base.Type_util.strip_cpp_ref_const t with
  | Some t -> (
    match Cpp_ir.Arrows.of_type t with
    | Some a -> Typed.v ~ty:(Closure a) e
    | None -> Typed.typed t e )
  | None -> Typed.untyped e

(** [adapted ~before into e]: [e], built from the typed value [before] to
    fill a slot of type [into]: [before] itself where nothing was built,
    and otherwise the adapter, at the slot's type. *)
let adapted ~(before : Typed.t) into e = if e == before.expr then before else adapted_to into e

(** [adapted_or_node into e]: [e], an adapter built for a slot of type
    [into] where there is one, and otherwise at the type its node carries. *)
let adapted_or_node into e = match into with Some _ -> adapted_to into e | None -> Typed.of_node e

(** The type of a value whose Core type is [t], converted in the scope of
    [env]. *)
let core_value_type cx env (t : Core.Type.t option) : Cpp_ir.Lowered.Value_type.t =
  match t with
  | Some t -> (
    try Typed (Types.cpp_of_core cx env t) with e when CErrors.noncritical e -> Deduced Not_yet_typed )
  | None -> Deduced Not_yet_typed

(** The type of the global [x] named as a value, its Core type instantiated
    at the use as [t]: a function's name, its parameters in the one group
    its declaration takes them in and any arrows its result has curried, or
    a value's declared type. *)
let global_value_type cx env x (t : Core.Type.t option) : Cpp_ir.Lowered.Value_type.t =
  match core_value_type cx env t with
  | Typed (Function (dom, cod)) -> (
    match Cpp_ir.Arrows.of_type (Function (dom, Cpp_ir.Types.spell_arrows Through_tvar cod)) with
    | Some a -> Function_name (x, a)
    | None -> Deduced Not_yet_typed )
  | v -> v

(** The Core type the inductive or type constant [r] is, unapplied. *)
let inductive_type r : Core.Type.t = Global_app {head = r; type_arguments = []; index_arguments = []}


(** The type a computation of Core type [t] yields when it runs: an action
    of a monad lowered sequentially returns its result. *)
let sequential_result (t : Core.Type.t) : Core.Type.t =
  match Base.Type_util.resolve_meta t with
  | Global_app {head; type_arguments; _} when Base.Table.is_monad head && not (Base.Table.is_monad_reified head) -> (
    match List.rev type_arguments with r :: _ -> r | [] -> t )
  | _ -> t

(** The Core type of the primitive type registered as [name]. *)
let primitive_core_type name =
  if Rocqlib.has_ref name then Some (inductive_type (Rocqlib.lib_ref name)) else None

(** The type of a literal of the primitive type registered as [name]. *)
let primitive_type cx env name = core_value_type cx env (primitive_core_type name)

(** [Corelib.Array.PrimArray.array], which registers no name. *)
let primitive_array =
  lazy
    (let dp = Names.DirPath.make (List.map Names.Id.of_string ["PrimArray"; "Array"; "Corelib"]) in
     Names.Constant.make1 (Names.KerName.make (Names.ModPath.MPfile dp) (Names.Label.make "array")))

(** The Core type of [e], read off the term where it says
    ({!Core_plan.Query.infer_core_body_type}), off the binder environment
    for a variable and a local function's application, off the target of a
    coercion, and off the value a boundary holds. *)
let rec core_type_of cx (e : Core.Expr.t) : Core.Type.t option =
  match e with
  | Coerce {target_type; _} -> Some target_type
  | Bound_variable {index; _} -> Lowering_state.get_env_type_opt cx index
  | Apply {callee = Bound_variable {index; _}; arguments} ->
    Option.bind (Lowering_state.get_env_type_opt cx index)
      (Base.Type_util.strip_arrows_n (Base.Type_util.count_real_core_args arguments))
  | Boxed_value {value; _} | Lambda_group_barrier {value; _} -> core_type_of cx value
  | Apply {callee = Global use; arguments}
    when Core_plan.Elaborate.static_projection_call ~walk:(Lowering_state.elaborations cx)
           ~lex:(Lowering_state.current_lexenv cx ()) use arguments <> None -> (
    match Core_plan.Elaborate.static_projection_call ~walk:(Lowering_state.elaborations cx)
            ~lex:(Lowering_state.current_lexenv cx ()) use arguments with
    | Some {codomain = Some cod; missing; _} ->
      Some (List.fold_right (fun d r -> Core.Type.Arrow {parameter = d; result = r}) missing cod)
    | _ -> None )
  | Fixpoint g | Cofixpoint g -> Some (Core.Recursion.Group.selected_member g).type_
  | Lambda {parameter; parameter_type; body} ->
    Option.map
      (fun result -> Core.Type.Arrow {parameter = parameter_type; result})
      (under cx (parameter, parameter_type) body)
  | Let {binder; binder_type; body; _} -> under cx (binder, binder_type) body
  | Numeral {inductive; _} -> Some (inductive_type inductive)
  | String _ -> primitive_core_type "strings.pstring.type"
  | UInt63 _ -> primitive_core_type "num.int63.type"
  | Float64 _ -> primitive_core_type "num.float.type"
  | Persistent_array {default; _} ->
    Option.map
      (fun t : Core.Type.t ->
        Global_app {head = Names.GlobRef.ConstRef (Lazy.force primitive_array); type_arguments = [t]; index_arguments = []})
      (core_type_of cx default)
  | Apply {callee = (Fixpoint _ | Cofixpoint _) as f; arguments} ->
    Option.bind (core_type_of cx f) (Base.Type_util.strip_arrows_n (Base.Type_util.count_real_core_args arguments))
  | Apply {callee; arguments} -> (
    match Core_plan.Query.infer_core_body_type e with
    | Some _ as t -> t
    | None ->
      Option.bind (core_type_of cx callee)
        (Base.Type_util.strip_arrows_n (Base.Type_util.count_real_core_args arguments)) )
  | _ -> Core_plan.Query.infer_core_body_type e

(** {!core_type_of} [body], under the binder [x] of type [t]: the binder
    environment is put back as it was. *)
and under cx (x, t) body =
  Lowering_state.with_scope cx (fun () ->
      Lowering_state.push_env_types cx [(Base.Core_util.id_of_binder_name x, t)];
      core_type_of cx body )

(** The type of a callable of type [f] given [n] arguments: what is left
    once its groups take them, a group straddled leaving a function of the
    rest. *)
let applied (f : Cpp_ir.Lowered.Value_type.t) n : Cpp_ir.Lowered.Value_type.t =
  let rec take (groups : Cpp_ir.Lowered.Type.t list list) result n : Cpp_ir.Lowered.Type.t option =
    match groups with
    | _ when n = 0 -> Some (Cpp_ir.Arrows.to_type {groups; result})
    | g :: rest when List.length g <= n -> take rest result (n - List.length g)
    | g :: rest -> Some (Cpp_ir.Arrows.to_type {groups = List.filteri (fun i _ -> i >= n) g :: rest; result})
    | [] -> (
      match Cpp_ir.Arrows.of_type result with
      | Some a -> take a.groups a.result n
      | None -> None )
  in
  match Cpp_ir.Value_type.arrows f with
  | Some a -> ( match take a.groups a.result n with Some t -> Typed t | None -> Deduced Not_yet_typed )
  | None -> Deduced Not_yet_typed

(** [of_built e x]: [x], lowered from [e] by a form module that does not
    type its result yet, at the type its outermost node carries, and failing
    that at the conversion of [e]'s Core type -- a closure grouped as the
    lambda it is, where [x] is one.  The census counts the second kind. *)
let of_built cx env (e : Core.Expr.t) (x : Cpp_ir.Lowered.Expr.t) : Typed.t =
  (* An action of a sequential monad is a call that runs it: what it yields
     is its result, whatever the call node recorded of the action's type. *)
  let action =
    match e with
    | Apply _ | Global _ -> (
      match Core_plan.Query.infer_core_body_type e with
      | Some t when sequential_result t != t -> Some (sequential_result t)
      | _ -> None )
    | _ -> None
  in
  match (Typed.of_node x, action) with
  | _, Some result -> Typed.v ~ty:(core_value_type cx env (Some result)) x
  | {ty = Deduced Not_yet_typed; _}, None -> (
    let derived =
      match (core_value_type cx env (core_type_of cx e), e) with
      | Deduced Not_yet_typed, Apply {callee = Bound_variable {index; _}; arguments} ->
        let callee : Cpp_ir.Lowered.Value_type.t =
          match Binders.read_value_type cx env index with
          | Typed t -> Typed (Types.unfold_cpp_typedef cx env t)
          | v -> v
        in
        applied callee (Base.Type_util.count_real_core_args arguments)
      | v, _ -> v
    in
    Base.Probe.hit "typed-derived" (fun () -> form_name e ^ " " ^ kind_name derived);
    match (x, derived) with
    | Lambda l, Typed t -> (
      match Cpp_ir.Arrows.of_type t with
      | Some a ->
        let doms, result = Cpp_ir.Arrows.curried a in
        let n = List.length l.params in
        if List.length doms < n then Typed.v ~ty:derived x
        else
          let rest = List.filteri (fun i _ -> i >= n) doms in
          let result = List.fold_right (fun d r -> Cpp_ir.Type.Function ([d], r)) rest result in
          Typed.v ~ty:(Closure {groups = [List.map fst l.params]; result}) x
      | None -> Typed.v ~ty:derived x )
    | _ -> Typed.v ~ty:derived x )
  | typed, None -> typed

(** Where lowering is, for a census line: the library and the declaration
    whose body is lowered. *)
let site cx =
  Base.Probe.library () ^ " "
  ^ match cx.Lowering_state.ctx.input.body_owner with
    | Some r -> Names.Id.to_string (Names.Label.to_id (Base.Common.label_of_r r))
    | None -> "-"

(** A short description of [e]'s head, for a census line. *)
let rec describe : Core.Expr.t -> string = function
  | Global {callee; _} -> "global:" ^ Names.Id.to_string (Names.Label.to_id (Base.Common.label_of_r callee))
  | Apply {callee; arguments} -> "apply/" ^ string_of_int (List.length arguments) ^ ":" ^ describe callee
  | Bound_variable {index; _} -> "var:" ^ string_of_int index
  | Lambda {body; _} -> "fun." ^ describe body
  | Let {body; _} -> "let." ^ describe body
  | e -> form_name e

(** The outermost constructor of a lowered expression, for a census line. *)
let rec node_name : Cpp_ir.Lowered.Expr.t -> string = function
  | Call (_, f, args) -> "call/" ^ string_of_int (List.length args) ^ "(" ^ node_name f ^ ")"
  | Entity _ -> "entity"
  | Local _ -> "local"
  | Scope _ -> "scope"
  | Lambda _ -> "lambda"
  | Literal _ -> "literal"
  | Member _ -> "member"
  | Move e -> "move(" ^ node_name e ^ ")"
  | Runtime _ -> "runtime"
  | Foreign_text _ -> "foreign"
  | Unbox _ -> "unbox"
  | Any_cast _ -> "any_cast"
  | Convert _ -> "convert"
  | Function_value _ -> "function_value"
  | Erase_callable _ -> "erase"
  | Abort _ -> "abort"
  | Aggregate _ -> "aggregate"
  | Converting_construct _ -> "converting_construct"
  | _ -> "other"

(** [census ?expected_ty e x] is [x], the typed lowering of [e], counted by
    [e]'s form and the kind of type [x] has, and where the position stated
    a type, by whether {!Coerce.decide} finds [x] fits it. *)
let census cx ?expected_ty e (x : Typed.t) =
  if Base.Probe.enabled () then begin
    Base.Probe.hit "typed" (fun () -> form_name e ^ " " ^ kind_name x.ty);
    if Cpp_ir.Value_type.not_yet_typed x.ty then
      Base.Probe.hit "typed-untyped" (fun () -> form_name e ^ " " ^ site cx ^ " " ^ describe e ^ " " ^ node_name x.expr);
    Option.iter
      (fun t ->
        let verdict =
          match Coerce.decide cx x.ty (Exactly t) with
          | _ when Base.Type_util.contains_tvar t -> "unchecked (slot at type variables)"
          | None when Coerce.unrelated cx x.ty (Exactly t) ->
            "unrelated in " ^ site cx ^ " " ^ describe e ^ " from " ^ Binders.show_value_type x.ty ^ " into " ^ Binders.type_shape t
          | None -> "fits"
          | Some p when Coerce.implicit x.ty p -> "fits-implicitly"
          | Some p -> Cpp_ir.Coercion.plan_name p ^ " in " ^ site cx ^ " " ^ describe e ^ " from " ^ Binders.show_value_type x.ty ^ " into " ^ Binders.type_shape t
        in
        Base.Probe.hit "typed-fit" (fun () -> form_name e ^ " " ^ verdict) )
      expected_ty
  end;
  x

(** Under [CRANE_PROBE], the declaration agreement check: [x], put as it is
    in a slot of type [into] -- a variable declared at a type, a parameter
    -- needs no adapter by {!Coerce.decide}.  One that does is a latent
    bug, or a type synthesised wrong. *)
let agreement cx ~site (x : Typed.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  if Base.Probe.enabled () then
    let verdict =
      match Coerce.decide cx x.ty into with
      | None when Coerce.unrelated cx x.ty into -> "unrelated from " ^ Binders.show_value_type x.ty
      | None -> "fits"
      | Some p when Coerce.implicit x.ty p -> "fits-implicitly"
      | Some p ->
        let slot = match into with Exactly t -> Binders.type_shape t | _ -> "?" in
        Cpp_ir.Coercion.plan_name p ^ " in " ^ Base.Probe.library () ^ " from " ^ Binders.show_value_type x.ty
        ^ " into " ^ slot
    in
    Base.Probe.hit "typed-agree" (fun () -> site ^ " " ^ verdict)
