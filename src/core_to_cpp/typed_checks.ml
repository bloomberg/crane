(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Typing what a form module builds without a type of its own
    ({!of_built}), and the checks typed lowering is held to under
    [CRANE_CHECK_IR]: every form is typed ({!typed_lowering}), a declared
    binder agrees with its value ({!agreement}), and a value fits the slot
    it is put in ({!fit}, up to the checked-in allowlist). *)

module Typed = Cpp_ir.Typed

(** The name of [e]'s form, for a violation. *)
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

(** [adapted_to t e]: [e], an adapter built to fill a slot of type [t], at
    that type: a closure grouped as [t] where [t] is a function type. *)
let adapted_to (t : Cpp_ir.Lowered.Type.t option) e =
  match Option.map Base.Type_util.strip_cpp_ref_const t with
  | Some t -> (
    match Cpp_ir.Arrows.of_type t with
    | Some a -> Typed.v ~ty:(Closure a) e
    | None -> Typed.typed t e )
  | None -> Typed.v ~ty:Typed.unannotated e

(** [adapted ~before into e]: [e], built from the typed value [before] to
    fill a slot of type [into]: [before] itself where nothing was built,
    and otherwise the adapter, at the slot's type. *)
let adapted ~(before : Typed.t) into e = if e == before.expr then before else adapted_to into e

(** [adapted_or_node ~fallback into e]: [e], an adapter built for a slot of
    type [into] where there is one, and otherwise at the type its node
    carries, or [fallback]. *)
let adapted_or_node ~fallback into e = match into with Some _ -> adapted_to into e | None -> Typed.of_node ~fallback e

(** The type of a value whose Core type is [t], converted in the scope of
    [env]. *)
let core_value_type cx env (t : Core.Type.t option) : Cpp_ir.Lowered.Value_type.t =
  match t with
  | Some t -> (
    try Typed (Types.cpp_of_core cx env t) with e when CErrors.noncritical e -> Deduced Untranslated )
  | None -> Deduced Untranslated

(** The type of the global [x] named as a value, its Core type instantiated
    at the use as [t]: a function's name, its parameters in the one group
    its declaration takes them in and any arrows its result has curried, or
    a value's declared type. *)
let global_value_type cx env x (t : Core.Type.t option) : Cpp_ir.Lowered.Value_type.t =
  match core_value_type cx env t with
  | Typed (Function (dom, cod)) -> (
    match Coerce.name_arrows dom cod with
    | Some a -> Function_name (x, a)
    | None -> Deduced Untranslated )
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
    Option.bind (core_type_of cx f)
      (Base.Type_util.strip_arrows_through_aliases (Base.Type_util.count_real_core_args arguments))
  | Apply {callee; arguments} -> (
    match Core_plan.Query.infer_core_body_type e with
    | Some _ as t -> t
    | None ->
      Option.bind (core_type_of cx callee)
        (Base.Type_util.strip_arrows_through_aliases (Base.Type_util.count_real_core_args arguments)) )
  | _ -> Core_plan.Query.infer_core_body_type e

(** {!core_type_of} [body], under the binder [x] of type [t]: the binder
    environment is put back as it was. *)
and under cx (x, t) body =
  Lowering_state.with_scope cx (fun () ->
      Lowering_state.push_env_types cx [(Base.Core_util.id_of_binder_name x, t)];
      core_type_of cx body )

(** The Core type [e] yields, where it is an action of a sequential monad:
    a call that runs it, so what it yields is its result, whatever the call
    node recorded of the action's type. *)
let sequential_action (e : Core.Expr.t) =
  match e with
  | Apply _ | Global _ -> (
    match Core_plan.Query.infer_core_body_type e with
    | Some t when sequential_result t != t -> Some (sequential_result t)
    | _ -> None )
  | _ -> None

(** [of_built e x]: [x], lowered from [e] by a form module that does not
    type its result yet, at the type its outermost node carries, and failing
    that at the conversion of [e]'s Core type -- a closure grouped as the
    lambda it is, where [x] is one. *)
let of_built cx env (e : Core.Expr.t) (x : Cpp_ir.Lowered.Expr.t) : Typed.t =
  match (Typed.carried x, sequential_action e) with
  | _, Some result -> Typed.v ~ty:(core_value_type cx env (Some result)) x
  | None, None -> (
    let derived =
      match (core_value_type cx env (core_type_of cx e), e) with
      | Deduced Untranslated, Apply {callee = Bound_variable {index; _}; arguments} ->
        let callee : Cpp_ir.Lowered.Value_type.t =
          match Binders.read_value_type cx env index with
          | Typed t -> Typed (Types.unfold_cpp_typedef cx env t)
          | v -> v
        in
        Option.default (Deduced Untranslated : Cpp_ir.Lowered.Value_type.t)
          (Cpp_ir.Typed.applied callee (Base.Type_util.count_real_core_args arguments))
      (* [tt] applied: only an impossible branch of a dependent match
         writes it, and the crossing it stands under is an abort
         ({!Coerce.absurd_coercion}). *)
      | Deduced Untranslated, Apply {callee; _}
        when (match core_type_of cx callee with Some t -> Base.Type_util.core_type_is_unit t | None -> false) ->
        Never
      | v, _ -> v
    in
    match (x, derived, e) with
    (* A global function named, not called: its name, whatever spells it. *)
    | (Entity _ | Scope _ | Type_member _), Typed (Function _), Global {callee; _} ->
      Typed.v ~ty:(global_value_type cx env callee (core_type_of cx e)) x
    | Lambda l, Typed t, _ -> (
      match Cpp_ir.Arrows.of_type t with
      | Some a ->
        let doms, result = Cpp_ir.Arrows.curried a in
        let n = List.length l.params in
        if List.length doms < n then Typed.v ~ty:derived x
        else
          let rest = List.filteri (fun i _ -> i >= n) doms in
          let result = List.fold_right (fun d r -> Cpp_ir.Type.Function ([d], r)) rest result in
          Typed.v ~ty:(Closure {groups = [List.map fst l.params]; result}) x
      (* A coercion whose target is no callable (a value-indexed family at
         a function index) builds no box of its lambda: what it built is
         the closure, its result written nowhere. *)
      | None when (match e with Coerce _ -> true | _ -> false) ->
        Typed.v ~ty:(Closure {groups = [List.map fst l.params]; result = Auto}) x
      | None -> Typed.v ~ty:derived x )
    | _ -> Typed.v ~ty:derived x )
  | Some ty, None -> Typed.v ~ty x

(** Where lowering is, for a violation: the declaration whose body is
    lowered, and with the library. *)
let declaration cx =
  match cx.Lowering_state.ctx.input.body_owner with
  | Some r -> Names.Id.to_string (Names.Label.to_id (Base.Common.label_of_r r))
  | None -> "-"

let site cx = Base.Probe.library () ^ " " ^ declaration cx

(** A short description of [e]'s head, for a violation. *)
let rec describe : Core.Expr.t -> string = function
  | Global {callee; _} -> "global:" ^ Names.Id.to_string (Names.Label.to_id (Base.Common.label_of_r callee))
  | Apply {callee; arguments} -> "apply/" ^ string_of_int (List.length arguments) ^ ":" ^ describe callee
  | Bound_variable {index; _} -> "var:" ^ string_of_int index
  | Lambda {body; _} -> "fun." ^ describe body
  | Let {body; _} -> "let." ^ describe body
  | e -> form_name e

(** What {!Coerce.decide} says of [x] put in the slot [into], where both
    state a type they can be compared at (the slot mentions no type
    variable, which the two may number differently): [None] elsewhere. *)
let verdict cx (x : Typed.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  match into with
  | Exactly t when not (Cpp_ir.Value_type.unstated x.ty || Base.Type_util.contains_tvar t) -> (
    match Coerce.decide cx x.ty into with
    | None when Coerce.unrelated cx x.ty into -> Some `Unrelated
    | None -> Some `Fits
    | Some p when Coerce.implicit ~al:(Coerce.aliases_in cx) x.ty p -> Some `Fits
    | Some p -> Some (`Plan p) )
  | _ -> None

let verdict_name = function
  | `Unrelated -> "unrelated"
  | `Plan p -> Cpp_ir.Coercion.decision_name p

(** [typed_lowering e x] is [x], the typed lowering of [e]; under
    [CRANE_CHECK_IR], a form lowered without a type is a violation. *)
let typed_lowering cx e (x : Typed.t) =
  if Base.Probe.checking () && Cpp_ir.Value_type.unstated x.ty then
    Base.Probe.violation "typed lowering"
      Pp.(str "a " ++ str (form_name e) ++ str " lowered without a type, in " ++ str (site cx) ++ str ": "
          ++ str (describe e));
  x

(** The pairs the fit check lets through: [unit_tests/typed_fit_allowlist.txt],
    one tab-separated [library, declaration, position, verdict, from, into]
    per line, built into the plugin.  Each is a type reconstruction defect
    still open; the list may only shrink. *)
let fit_allowlist =
  lazy
    (let t = Hashtbl.create 512 in
     List.iter
       (fun l -> if l <> "" && l.[0] <> '#' then Hashtbl.replace t l ())
       (String.split_on_char '\n' Typed_fit_allowlist.text);
     t)

(** The open defect class a pair belongs to by its structure alone,
    whatever declaration it is met in: [x], put in a slot of type [into],
    which {!verdict} found unrelated.  Each class is a type reconstruction
    defect whose C++ is right -- the slot is spelled through a name C++
    resolves to the value's type -- and is recognised by the relation
    between the two types that makes it so, never by a name:

    - [event]: an event family named unapplied ([getE]) against its
      application to an index ([app(getE)<nat>]): the slot is the family
      applied, the value the family;
    - [carrier]: a higher-kinded carrier applied ([app(M)<A>]) against a type
      whose trailing type arguments are [A]: the slot is the carrier's
      application, which unfolds to the value's type;
    - [itreeF]: the observation of an interaction tree ([itreeF]) against
      the tree ([itree], or an alias of a tree's type);
    - [promoted]: two types that agree once every member of an instance or
      a class ([_tcI0::iptr], [ProvenanceV<>::prov]) and every promoted
      variable in them is taken as undecided: an associated type C++
      resolves through the instance, which lowering wrote on one side and
      resolved on the other.

    Any other pair is no known class: on {!fit_allowlist} or fatal. *)
let known_class cx (x : Typed.t) (into : Cpp_ir.Lowered.Slot_type.t) : string option =
  let related a b = not (Coerce.unrelated cx (Typed a) (Exactly b)) in
  let rec bare (t : Cpp_ir.Lowered.Type.t) =
    match t with Const t | Reference (_, t) | In_namespace (_, t) -> bare t | t -> t
  in
  let is_ind name (t : Cpp_ir.Lowered.Type.t) =
    match bare t with
    | Entity_application ((Names.GlobRef.IndRef _ as g), _, _) ->
      String.equal (Pp.string_of_ppcmds (Names.GlobRef.print g)) ("(ITree.Core.ITreeDefinition." ^ name ^ ", 0)")
    | _ -> false
  in
  let rec last n l = if List.length l <= n then l else last n (List.tl l) in
  match (x.ty, into) with
  | Typed from, Exactly slot -> (
    match (bare from, bare slot) with
    | (Entity_application (_, [], _) as f), Apply (h, _ :: _) when related f h -> Some "event"
    | Entity_application (_, targs, _), Apply (_, (_ :: _ as args))
      when List.length targs >= List.length args && List.for_all2 related (last (List.length args) targs) args ->
      Some "carrier"
    | f, s when is_ind "itreeF" f && (is_ind "itree" s || match s with Entity_application (Names.GlobRef.ConstRef _, _, _) -> true | _ -> false) ->
      Some "itreeF"
    | _ ->
      let members = ref false in
      let undecided =
        Cpp_ir.Types.map (function
          | Cpp_ir.Type.Member ((Instance _ | Entity_application _), _) as m
            when (match m with
                  | Member (Entity_application (g, _, _), _) -> Base.Table.is_typeclass g || Base.Table.builds_instance g
                  | _ -> true ) ->
            members := true;
            Cpp_ir.Type.Any
          | Promoted_member _ -> members := true; Cpp_ir.Type.Any
          | t -> t )
      in
      let from' = undecided from and slot' = undecided slot in
      if !members && related from' slot' then Some "promoted" else None )
  | _ -> None

(** [s] on one line, its whitespace runs one space: a type's shape as
    {!fit_allowlist} keys it. *)
let one_line s =
  String.concat " " (List.filter (( <> ) "") (String.split_on_char ' ' (String.map (function '\n' | '\t' -> ' ' | c -> c) s)))

(** The fit check, fatal under [CRANE_CHECK_IR]: [x], as it is put in the
    slot [into] at [site] -- a destination of statements, an argument at its
    parameter -- needs no adapter by {!Coerce.decide}, and its type is
    related to the slot's.  A pair on {!fit_allowlist} is let through and
    counted under [CRANE_PROBE] as [typed-fit-allowed], so that a census
    finds the entries no longer hit
    ([scripts/check-typed-fit-allowlist.sh]). *)
let fit cx ~site (x : Typed.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  if Base.Probe.checking () then
    match verdict cx x into with
    | Some ((`Unrelated | `Plan _) as verdict) ->
      let slot = match into with Exactly t -> Binders.type_shape t | _ -> "?" in
      let key =
        String.concat "\t"
          (List.map one_line [Base.Probe.library (); declaration cx; site; verdict_name verdict; Binders.show_value_type x.ty; slot])
      in
      let known = match verdict with `Unrelated -> known_class cx x into | `Plan _ -> None in
      if Option.has_some known then Base.Probe.hit "typed-fit-class" (fun () -> Option.get known ^ "\t" ^ key)
      else if Hashtbl.mem (Lazy.force fit_allowlist) key then Base.Probe.hit "typed-fit-allowed" (fun () -> key)
      else
        Base.Probe.violation "typed fit"
          Pp.(str "a value of type " ++ str (Binders.show_value_type x.ty) ++ str " put in a slot of type "
              ++ str slot ++ str " (" ++ str site ++ str ", " ++ str (verdict_name verdict) ++ str ") in "
              ++ str (Base.Probe.library ()) ++ str " " ++ str (declaration cx)
              ++ str "; not in unit_tests/typed_fit_allowlist.txt as: " ++ str key)
    | _ -> ()

(** The declaration agreement check, fatal under [CRANE_CHECK_IR]: [x], put as it is
    in a slot of type [into] -- a variable declared at a type, a parameter
    -- needs no adapter by {!Coerce.decide}.  One that does is a latent
    bug, or a type synthesised wrong. *)
let agreement cx ~site (x : Typed.t) (into : Cpp_ir.Lowered.Slot_type.t) =
  if Base.Probe.checking () then (
    let slot = match into with Exactly t -> Binders.type_shape t | _ -> "?" in
    match Coerce.decide cx x.ty into with
    | None when Coerce.unrelated cx x.ty into ->
      Base.Probe.violation "binder agreement"
        Pp.(str site ++ str ": a value of type " ++ str (Binders.show_value_type x.ty) ++ str " declared at "
            ++ str slot)
    | Some p when not (Coerce.implicit ~al:(Coerce.aliases_in cx) x.ty p) ->
      Base.Probe.violation "binder agreement"
        Pp.(str site ++ str ": a value of type " ++ str (Binders.show_value_type x.ty) ++ str " declared at "
            ++ str slot ++ str " without the " ++ str (Cpp_ir.Coercion.decision_name p) ++ str " it needs")
    | _ -> () );
