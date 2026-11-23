(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Pure predicates and transforms over Core types ([Core.Type.t]) and CppIR
    types ([Cpp_ir.Lowered.Type.t]), shared by extraction, lowering,
    declaration generation and the printer.  See [type_util.mli]. *)

open Common
open Names
open Core_util
open Table

(** Derive the PascalCase C++ constructor struct name from a [GlobRef.t].
    Constructor references (e.g. [ConstructRef ((kn,0), 1)] for [Cons]) are
    rendered as capitalized versions of their Rocq name; other references
    fall back to [Ctor<i>]. Used at both definition sites (struct generation)
    and access sites (pattern matching, record reuse) to obtain the key for
    {!Common.lookup_ctor_field_name}.

    @param fallback_idx  index used when the reference is not a [ConstructRef]
    @param c             the global reference to look up *)
let ctor_struct_name_of_ref ?(fallback_idx = 0) (c : GlobRef.t) : string =
  match c with
  | GlobRef.ConstructRef _ ->
    String.capitalize_ascii (Common.pp_global_name Type c)
  | _ -> ctor_fallback_name fallback_idx

(** [instance_type_args args] -- a typeclass's type arguments as both the
    instance's signature and its call sites must spell them.

    Extraction erases a type that carries no information ([Inductive token :=
    tok]) all the way to [Core.Type.Erased], and a parameter at such a type would then
    disappear.  It may not: the class declares each field at an arity the
    generated concept checks, so the parameter keeps its slot at the erased
    type -- which is how the concept spells it for that instance too
    ([C<ic, std::any>]). *)
let instance_type_args (args : _ Core.Type.at list) : _ Core.Type.at list =
  List.map (fun t -> if Core_util.is_erased_type t then Core.Type.Unknown else t) args

(** Like {!ctor_struct_name_of_ref} but returns an [Core.Binder_name.Source.t]. *)
let ctor_struct_id_of_ref ?(fallback_idx = 0) (c : GlobRef.t) : Id.t =
  Id.of_string (ctor_struct_name_of_ref ~fallback_idx c)

(** Resolve a chain of [Core.Type.Meta] indirections to the underlying type. *)
let rec resolve_meta = function
  | Core.Type.Meta {contents = Some t} -> resolve_meta t
  | t -> t

(** Unfold a type alias standing for a function type.

    A definition may be typed by name -- [Definition to_nat (c : church)] --
    and everything that reads a callee's parameter types off arrows has to see
    the arrows the name stands for.  Only function bodies are unfolded: any
    other alias is a type in its own right and its spelling is worth keeping.

    Note the caller may need the fully applied form, so the alias's own type
    arguments are substituted for the body's variables. *)
let rec expand_core_fun_alias ty =
  match resolve_meta ty with
  | Core.Type.Global_app {head = GlobRef.ConstRef kn; type_arguments = args; _} as t ->
    ( match Table.lookup_typedef_unchecked kn with
    | Some body ->
      let body = Core.Widen.type_ body in
      let body =
        if args = [] then body else Core_util.type_subst_list args body
      in
      ( match resolve_meta body with
      | Core.Type.Arrow _ -> expand_core_fun_alias body
      | _ -> t )
    | None -> t )
  | t -> t

(** Unify a template C++ type with a concrete one to extract type variable
    bindings. Recursively walks matching type constructors
    ([Entity_application], [Function], [Reference], [Const], [In_namespace])
    and collects [(id, concrete_ty)] pairs wherever [tmpl] has a named
    [Variable].

    @param tmpl  the template type (may contain [Variable] holes)
    @param conc  the concrete type to unify against
    @return association list of type variable bindings *)
let rec extract_tvar_map (tmpl : Cpp_ir.Lowered.Type.t) (conc : Cpp_ir.Lowered.Type.t) :
    (Names.Id.t * Cpp_ir.Lowered.Type.t) list =
  match (tmpl, conc) with
  | Variable (Index (_, Some id) | Named id), _ -> [(id, conc)]
  | Entity_application (g1, tys1, _), Entity_application (g2, tys2, _)
    when globref_equal g1 g2 && List.length tys1 = List.length tys2 ->
    List.concat (List.map2 extract_tvar_map tys1 tys2)
  | Function (args1, ret1), Function (args2, ret2) when List.length args1 = List.length args2 ->
    List.concat (List.map2 extract_tvar_map args1 args2) @ extract_tvar_map ret1 ret2
  | Reference (k1, t1), Reference (k2, t2) when k1 = k2 -> extract_tvar_map t1 t2
  | Const t1, Const t2 -> extract_tvar_map t1 t2
  | In_namespace (_, t1), In_namespace (_, t2) -> extract_tvar_map t1 t2
  | In_namespace (_, t1), t2 | t1, In_namespace (_, t2) -> extract_tvar_map t1 t2
  | _ -> []

(** Search a Core type for the first self-referential or mutually-recursive
    subtype, returning its type arguments. Recurses into [Core.Type.Global_app] type
    arguments and resolves [Core.Type.Meta] indirections.

    @param is_self_or_mutual  predicate identifying self/mutual references
    @return [Some args] for the first matching [Core.Type.Global_app], or [None] *)
let rec find_self_ref_args ~is_self_or_mutual = function
  | Core.Type.Global_app {head = r; type_arguments = args; _} when is_self_or_mutual r -> Some args
  | Core.Type.Global_app {type_arguments = args; _} ->
    List.find_map (find_self_ref_args ~is_self_or_mutual) args
  | Core.Type.Meta {contents = Some t} -> find_self_ref_args ~is_self_or_mutual t
  | _ -> None

(** Check if a Core type is directly erased (non-recursive, top-level only).
    Matches an unresolved [Core.Type.Meta], a [Core.Type.Open] hole, [Core.Type.Erased], and a
    [Core.Type.Rigidity.Schematic] [Core.Type.Variable]. *)
let is_erased_core_type = function
  | Core.Type.Meta {contents = None}
  | Core.Type.Open _
  | Core.Type.Erased _
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; _} -> true
  | _ -> false

(** Recursive check for erased sub-types inside a Core type.  Resolves [Core.Type.Meta]
    chains before checking, then recurses into [Core.Type.Global_app] type arguments.

    An arrow is opaque by default: the metas of a function type are the callee's
    own business, and treating them as erasure here would make every stored
    closure look erased to callers that only care about the data around it.
    [~in_arrows:true] looks through them, for a caller asking whether a type is
    concrete enough to be spelled -- the closure inside
    [option (nat -> nat)] is exactly what such a caller must not miss. *)
let rec core_type_contains_erased ?(in_arrows = false) ty =
  let recur = core_type_contains_erased ~in_arrows in
  match resolve_meta ty with
  | Core.Type.Meta _
  | Core.Type.Open _
  | Core.Type.Erased _
  | Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; _} -> true
  | Core.Type.Global_app {type_arguments = tys; _} -> List.exists recur tys
  | Core.Type.Arrow {parameter = a; result = b} -> in_arrows && (recur a || recur b)
  | _ -> false

(** Whether a type variable survives anywhere in [ty].

    A variable the surrounding substitution did not reach names a template
    parameter that is not in scope where the type will be spelled, so a caller
    weighing whether an instantiated type is usable as a concrete expectation
    must reject it: converting it prints an undeclared [T1]. *)
let rec core_type_contains_tvar ty =
  match resolve_meta ty with
  | Core.Type.Variable _ -> true
  | Core.Type.Global_app {type_arguments = tys; _} | Core.Type.Variable_app {arguments = tys; _} ->
    List.exists core_type_contains_tvar tys
  | Core.Type.Arrow {parameter = a; result = b} -> core_type_contains_tvar a || core_type_contains_tvar b
  | _ -> false

(** Return the codomain of a Core type, chasing through arrows and meta
    indirections. For [A -> B -> C] this returns [C]. *)
let rec core_codomain = function
  | Core.Type.Arrow {result = t2; _} -> core_codomain t2
  | Core.Type.Meta {contents = Some t} -> core_codomain t
  | t -> t

(* The registered monad heading [ty] seen through aliases, after [codomain]
   (arrows peeled, at every alias's expansion) or [resolve_meta] (a function
   type is no monad, however it is spelled). *)
let rec monad_heading view ty =
  match view ty with
  | Core.Type.Global_app {head = m; _} when Table.is_monad m -> Some m
  | Core.Type.Global_app {head = GlobRef.ConstRef kn; type_arguments = args; _} -> (
    match Table.lookup_typedef_unchecked kn with
    | Some body ->
      let body = Core.Widen.type_ body in
      monad_heading view (if args = [] then body else Core_util.type_subst_list args body)
    | None -> None )
  | _ -> None

let codomain_monad t = monad_heading core_codomain t

let type_monad t = monad_heading resolve_meta t

(** Why a binder -- a lambda's, a fixpoint's, a declaration's domain -- is
    not a parameter at run time.  Extraction erases a binder whose type is a
    type, a proof, or an argument declared implicit ([Crane Extraction
    Implicit]); every argument list drops it, an [Core.Expr.Erased_value] standing for its
    argument.  A binder of [void] type survives extraction but takes no C++
    parameter. *)
type erasure =
  | Type_binder
  | Proof
  | Implicit of GlobRef.t * int
  | Void

(** What a binder is at run time: a parameter, or erased for the
    {!erasure} given.  See {!binder_role}. *)
type binder_role =
  | Runtime
  | Erased of erasure

(** The erasure extraction recorded in a binder's type, if it did: its
    [Core.Type.Erased], whose kill reason says why. *)
let extraction_erasure (ty : _ Core.Type.at) : erasure option =
  match resolve_meta ty with
  | Core.Type.Erased Core.Erasure_reason.Type_argument -> Some Type_binder
  | Core.Type.Erased Core.Erasure_reason.Proof -> Some Proof
  | Core.Type.Erased (Core.Erasure_reason.Configured_implicit {entity = r; position = i}) -> Some (Implicit (r, i))
  | _ -> None

(** Whether extraction erased a binder of type [ty]: no call passes an
    argument for it. *)
let erased_by_extraction ty = Option.has_some (extraction_erasure ty)

(** The domains of a Core type, in argument order -- every arrow it has,
    including the erased ones, so a position in the result is a position in the
    type.  Callers that need the arguments a C++ call actually passes want
    {!core_value_domains}; callers indexing by type-variable position want this.

    Only the arrow spine is chased through metavariables; each domain is
    returned as written, since a caller that cares runs {!resolve_meta} on the
    one entry it looks at. *)
let rec core_domains t =
  match resolve_meta t with
  | Core.Type.Arrow {parameter = t1; result = t2} -> t1 :: core_domains t2
  | _ -> []

(** The domains of a Core type, in argument order, skipping the erased
    ([Core.Type.Erased]) ones -- so the result lines up with the arguments a C++ call
    actually passes. *)
let core_value_domains t =
  List.filter (fun d -> not (erased_by_extraction d)) (core_domains t)

let collect_typed_lams ty b =
  let n_type_dom = List.length (core_domains ty) in
  let all_ids, inner = collect_lams b in
  let n_excess = List.length all_ids - n_type_dom in
  if n_excess > 0 then
    (Util.List.skipn n_excess all_ids, named_lams (Util.List.firstn n_excess all_ids) inner)
  else (all_ids, inner)

let eta_parameters ty params =
  let doms = List.rev (core_domains ty) in
  let n_missing = max 0 (List.length doms - List.length params) in
  List.mapi (fun i t -> (Core.Binder_name.Source (eta_param_id (n_missing - 1 - i)), t))
    (Util.List.firstn n_missing doms)

let unwritten_parameters ty params body =
  let missing = eta_parameters ty params in
  ( match body with
  | Core.Expr.Axiom_value _ | Core.Expr.Runtime_error _ -> ()
  | _ ->
    if missing <> [] && Probe.checking () then
      Probe.violation "eta-expanded"
        Pp.(
          str "a definition binds " ++ int (List.length params) ++ str " of the "
          ++ int (List.length params + List.length missing)
          ++ str " parameters its type declares; Core_passes.Phase.normalize eta-expands every one" ) );
  missing

let declared_parameters ty b =
  let params, body = collect_typed_lams ty b in
  (unwritten_parameters ty params body @ params, body)

(** Give [b] as many binders as [ty] has value arrows.

    A body that stops short of its type -- [fun n => tfmap f] where the type
    asks for two arguments -- is a partial application, which is a term a
    functional language writes freely and a C++ slot of a known signature
    cannot hold.  The binders are added innermost, so the lambdas already
    written keep their names and only the ones the body never named are
    invented. *)
let eta_expand_to ty b =
  let doms = core_value_domains ty in
  let ids, inner = Core_util.collect_lams b in
  let k = List.length doms - List.length ids in
  if k <= 0 then b
  else
    let missing = List.filteri (fun i _ -> i >= List.length doms - k) doms in
    (* [collect_lams] and [named_lams] both count innermost first, and the
       binders missing from the body are the last of the type's domains. *)
    let extra =
      List.mapi
        (fun i t ->
          ( Core.Binder_name.Source (Names.Id.of_string (Printf.sprintf "_eta%d" (k - 1 - i))),
            t ) )
        (List.rev missing)
    in
    let args = List.init k (fun i -> Core.Expr.fresh_rel (k - i)) in
    Core_util.named_lams (extra @ ids)
      (Core_util.apply_eta_args (Core_util.ast_lift k inner) args)

(** A class method's type with the quantifier a concept erased put back.

    A class's [constructor_argument_types] entry has already erased the method's own [forall A]
    and the class instance itself; the projection constant kept both.  Reading
    the projection's type and dropping those leading domains recovers the
    method as its instances must spell it -- a member template, not a signature
    flattened to [std::any].  Both the instance side ({!Core_to_cpp.Lower_decl}) and the
    call side ({!Core_to_cpp.Lower_expr}) need the same answer, so they ask here. *)
let rec strip_erased_method_prefix = function
  | Core.Type.Arrow {parameter = d; result = rest} when Core_util.is_erased_type d || Table.is_typeclass_type d ->
    strip_erased_method_prefix rest
  | t -> t

(** How many of the class's parameters a projection takes in front of its
    dictionary: the erased arrows leading its type. *)
let projection_class_arity proj =
  let rec count = function
    | Core.Type.Arrow {parameter = d; result = b} when Core_util.is_erased_type d -> 1 + count b
    | Core.Type.Meta {contents = Some t} -> count t
    | _ -> 0
  in
  match Table.inspect_type proj {read = count} with exception Not_found -> 0 | n -> n

(** [method_tvar_count class_ref ty] is the arity of the member template an
    instance method of type [ty] emits: the type variables the method
    quantifies on its own, past the class's parameters.

    The instance's definition and the concept's requirement must agree on this
    number -- the definition binds that many [_A]s, and the requirement has to
    supply that many arguments -- so both read it from here. *)
let method_tvar_count class_ref ty =
  max 0 (Core_util.type_maxvar ty - List.length (Table.get_ind_ip_vars class_ref))

(** The arguments a higher-kinded carrier has already fixed: [Fn (prod X)]
    fixes the pair's first component, while the eta-expanded [option _] fixes
    nothing.  What is left is what the class still applies -- as the alias
    template's parameters, or as the method's own type variables. *)
let hkt_carrier_fixed_args arity core_ty =
  match core_ty with
  | Core.Type.Global_app {head = r; type_arguments = args; _} ->
    let given = List.length args in
    let total = max arity (max given (Table.get_type_scheme_arity r)) in
    let fixed = max 0 (total - arity) in
    if given >= fixed then CList.firstn fixed args else []
  | Core.Type.Variable_app {arguments = args; _} ->
    (* A carrier that is a type variable ([Instance ... (M : Type -> Type)])
       is eta-expanded the same way, but has no declared scheme to compare
       against: what it applies beyond [arity] is what it fixed. *)
    CList.firstn (max 0 (List.length args - arity)) args
  | _ -> []

(** [recover_method_quantifier class_ref field_ref erased] is the type of a
    class field with its own [forall A] intact.

    A class's [constructor_argument_types] entry has already erased the quantifier; the
    projection constant has not.  An instance method takes it back as a
    member template: a higher-kinded class's every method, whose carrier is an
    alias template applied to the element type, and a type class's method
    parametric in a type of its own -- [mapf : forall A, (A -> A) -> A -> A] --
    which is then typed at the caller's [A] instead of boxing through
    [std::any].  Anything else -- a plain record's field, a method with no
    type variable of its own -- comes back as [erased]. *)
let recover_method_quantifier class_ref field_ref erased =
  match Table.find_type field_ref with
  | exception Not_found -> erased
  | projection ->
    let recovered = strip_erased_method_prefix projection in
    if Table.get_ind_hkt_params class_ref <> [] then recovered
    else if
      Table.is_typeclass class_ref && method_tvar_count class_ref recovered > 0
    then recovered
    else erased

(** Whether an instance declares class field [field_ref] of [class_ref] as a
    member template: where {!recover_method_quantifier} takes the quantifier
    back.  Its arguments and result are then the method's own, not erased. *)
let method_is_member_template class_ref field_ref =
  Table.get_ind_hkt_params class_ref <> []
  || Table.is_typeclass class_ref
     &&
     match
       Table.inspect_type field_ref
         {read = (fun projection -> method_tvar_count class_ref (strip_erased_method_prefix projection) > 0)}
     with
     | exception Not_found -> false
     | b -> b

(** [core_drop_arrows n t] is what is left of [t] after [n] of its arrows have
    been applied. Erased ([Core.Type.Erased]) domains do not count, matching the value
    arrows a C++ call consumes. Fewer than [n] arrows leaves [Core.Type.Unknown], which
    no caller can mistake for a function type. *)
let rec core_drop_arrows n t =
  if n <= 0 then t
  else
    match t with
    | Core.Type.Arrow {parameter = t1; result = t2} when Core_util.is_erased_type t1 -> core_drop_arrows n t2
    | Core.Type.Arrow {result = t2; _} -> core_drop_arrows (n - 1) t2
    | Core.Type.Meta {contents = Some t} -> core_drop_arrows n t
    | _ -> Core.Type.Unknown

(** Count the number of non-erased (non-[Core.Type.Erased]) arrow levels in a Core type.
    For example [Core.Type.Erased -> A -> B -> C] counts as 2 (the dummy is skipped). *)
let count_core_value_arrows t = List.length (core_value_domains t)

(** Check if the codomain of a Core type (after all arrows) is a type variable.
    When true, the type variable might hide additional arrows, so the arrow
    count is not reliable for over-application detection. *)
let rec core_codomain_is_tvar = function
  | Core.Type.Arrow {result = t2; _} -> core_codomain_is_tvar t2
  | Core.Type.Meta {contents = Some t} -> core_codomain_is_tvar t
  | Core.Type.Variable _ | Core.Type.Unknown -> true
  | _ -> false

(** Count the total number of arrow levels in a Core type (including erased). *)
let rec count_core_arrows = function
  | Core.Type.Arrow {result = t2; _} -> 1 + count_core_arrows t2
  | _ -> 0

(** Check if a Core type is a monadic type (outermost constructor is a registered
    monad). Monadic non-function definitions are generated as zero-arg thunks,
    so bare references to them must be wrapped in a function call. *)
let is_monadic_core_type ty =
  match resolve_meta ty with
  | Core.Type.Global_app {head = r; _} -> Table.is_monad r
  | _ -> false

(** Check if a Core type is void (unit type mapped to C++ void). *)
let core_type_is_void (ty : _ Core.Type.at) : bool =
  match resolve_meta ty with
  | Core.Type.Global_app {head = r; _} -> is_void r
  | _ -> false

(** The role of a binder of type [ty]: the one classification every site
    asking whether a binder is a run-time parameter reads. *)
let binder_role (ty : _ Core.Type.at) : binder_role =
  match extraction_erasure ty with
  | Some e -> Erased e
  | None -> if core_type_is_void ty then Erased Void else Runtime

(** Whether a binder of type [ty] is a parameter at run time
    ({!binder_role}). *)
let is_runtime_binder_type (ty : _ Core.Type.at) : bool =
  match binder_role ty with Runtime -> true | Erased _ -> false

(** Whether a binder of type [ty] is erased for being [void]: it survives
    extraction, and an argument list keeps it, but a C++ signature does
    not. *)
let void_binder (ty : _ Core.Type.at) : bool =
  match binder_role ty with Erased Void -> true | Runtime | Erased _ -> false

(** Check if a Core type is Rocq's [unit] type. *)
let core_type_is_unit (ty : _ Core.Type.at) : bool =
  match resolve_meta ty with
  | Core.Type.Global_app {head = r; _} -> Table.is_unit_type r
  | _ -> false

(** Whether a function declaration's parameter of type [ty] is left out of
    its C++ signature, a call by name passing nothing for it: a [void] one
    ({!void_binder}), or a [unit] one, whose one value is known without being
    passed.  A callable value's parameter -- a lambda's, a [crane::fn]'s -- is
    kept: a polymorphic slot [A -> B] instantiated at [A := unit] calls it with
    a value. *)
let declaration_drops_binder (ty : Core.Type.t) : bool = void_binder ty || core_type_is_unit ty

(** Whether the declaration of type [decl_ty] leaves out its [i]th parameter
    (0-based, source order, erased ones counted), read off the declared domain
    as a call site reads it ({!declaration_drops_binder}): the binder's own
    type may say [unit] where the declaration names an alias, and an alias
    reached through a functor's argument is not [unit] inside the functor.
    [binder_ty] answers past the declared arrows. *)
let declaration_drops_parameter decl_ty i binder_ty =
  match List.nth_opt (core_domains decl_ty) i with
  | Some d -> declaration_drops_binder d
  | None -> declaration_drops_binder binder_ty

let own_type_variables ~n_outer tys =
  List.exists (fun ty -> Core_util.IntSet.exists (fun i -> i > n_outer) (Core_util.core_tvars ty)) tys

let is_cpp_unit_type : Cpp_ir.Lowered.Type.t -> bool = function
  | Entity_application ((GlobRef.IndRef _ as r), _, _) -> Table.is_unit_type r
  | In_namespace (r, _) -> Table.is_unit_type r
  | _ -> false

(** Check if a Core type represents a void or unit type. *)
let core_type_is_unit_or_void ty = core_type_is_void ty || core_type_is_unit ty

(** Filter out erased ([Core.Type.Erased]) types from a type list. *)
let filter_value_types l = List.filter (fun t -> not (is_erased_type t)) l

(** Test whether the codomain of a Core function type, after skipping [n]
    value-domain arrows, erases to [std::any] in the generated C++.

    A [Core.Type.Variable] or [Core.Type.Unknown] codomain erases to [std::any] only when
    at least one [Core.Type.Erased Core.Erasure_reason.Type_argument] was encountered while traversing the domain.
    That marker identifies a higher-rank, universally-quantified function (e.g.
    [forall A : Type, A -> A]) whose C++ encoding stores arguments and results
    as [std::any].  A plain [Core.Type.Variable i] with no preceding [Core.Type.Erased] is a named C++
    template parameter (e.g. [T2] in [T1 -> T2]) and must {b not} be treated
    as erased.

    [n] counts the value-domain arrows to skip before inspecting the codomain;
    pass [0] to query the type's immediate codomain.  The [?has_dummy] flag
    accumulates whether a [Core.Type.Erased Core.Erasure_reason.Type_argument] was seen; callers should omit it
    (defaults to [false]).  Note: [Core.Type.Erased Core.Erasure_reason.Proof] (erased proof) is skipped
    without setting [has_dummy] — a proof argument does not make the codomain
    [std::any]. *)
let rec core_codomain_erases_to_any ?(has_dummy = false) n = function
  | Core.Type.Arrow {parameter = t; result = rest} ->
    ( match t with
    | Core.Type.Erased Core.Erasure_reason.Type_argument ->
      core_codomain_erases_to_any ~has_dummy:true n rest
    | _ when is_erased_type t ->
      (* Core.Type.Erased Core.Erasure_reason.Proof /
         Core.Erasure_reason.Configured_implicit: erased proof/implicit, skip
         without setting has_dummy and without consuming a value-arg slot. *)
      core_codomain_erases_to_any ~has_dummy n rest
    | _ ->
      if n > 0 then core_codomain_erases_to_any ~has_dummy (n - 1) rest
      else false )
  | Core.Type.Variable _ | Core.Type.Unknown -> n = 0 && has_dummy
  | Core.Type.Meta {contents = Some t} -> core_codomain_erases_to_any ~has_dummy n t
  | _ -> false

(** [core_codomain_after n ty] is what [ty] returns once [n] value arguments
    have been applied, skipping erased (proof and type) domains as
    {!core_codomain_erases_to_any} does.  [None] where [ty] has fewer value
    arrows than that. *)
let rec core_codomain_after n = function
  | Core.Type.Arrow {parameter = t; result = rest} ->
    if is_erased_type t then core_codomain_after n rest
    else if n > 0 then core_codomain_after (n - 1) rest
    else Some (Core.Type.Arrow {parameter = t; result = rest})
  | Core.Type.Meta {contents = Some t} -> core_codomain_after n t
  | ty -> if n = 0 then Some ty else None

(** Return [true] if the C++ type contains any unresolved type variable
    ([Variable] or [Auto]): such a type has no spelling of its own at the
    use, so it cannot serve as a cast target or a concrete expected type. *)
let contains_tvar =
  Cpp_ir.Types.exists (fun (t : Cpp_ir.Lowered.Type.t) -> match t with Variable _ | Auto -> true | _ -> false)

(** Whether [g] is the standard library's [prod], by identity: a user's
    inductive of the same name is not the pair. *)
let is_prod_global g = Rocqlib.check_ref "core.prod.type" g

(** Structural equality on C++ types, ignoring [Const] and [In_namespace]
    wrappers and the name annotations of indexed [Variable]s.  Used to match
    the state parameter type
    against the state component of a [pair<S,R>] return type. *)
let rec cpp_ty_eq (t1 : Cpp_ir.Lowered.Type.t) (t2 : Cpp_ir.Lowered.Type.t) =
  let rec strip : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
    | Const t | In_namespace (_, t) -> strip t
    | t -> t
  in
  match (strip t1, strip t2) with
  | Entity_application (g1, ts1, _), Entity_application (g2, ts2, _) ->
    GlobRef.CanOrd.equal g1 g2 && List.length ts1 = List.length ts2 && List.for_all2 cpp_ty_eq ts1 ts2
  | Variable (Index (i1, _)), Variable (Index (i2, _)) -> i1 = i2
  | Variable (Named x1), Variable (Named x2) -> Id.equal x1 x2
  | Reference (Lvalue, t1'), Reference (Lvalue, t2') | Reference (Forwarding, t1'), Reference (Forwarding, t2') ->
    cpp_ty_eq t1' t2'
  | Shared_pointer t1', Shared_pointer t2' -> cpp_ty_eq t1' t2'
  | Function (d1, c1), Function (d2, c2) ->
    List.length d1 = List.length d2 && List.for_all2 cpp_ty_eq d1 d2 && cpp_ty_eq c1 c2
  | Void, Void | Auto, Auto | Any, Any -> true
  | _ -> false

(** Whether [g] is the standard library's [list], by identity. *)
let is_list_global g = Rocqlib.check_ref "core.list.type" g

(** Whether [g] is [list] under a custom mapping, so that its values are a C++
    container -- [std::deque<T>] and the like -- rather than a Crane inductive.
    Such a container has no converting constructor and no factory methods, so
    several printers have to build and take it apart element by element. *)
let is_custom_list_global g = is_list_global g && Table.is_custom g

let list_ctor_struct_names (g : GlobRef.t) : string * string =
  match g with
  | GlobRef.IndRef (kn, i) ->
    let nil_ref = GlobRef.ConstructRef ((kn, i), 1) in
    let cons_ref = GlobRef.ConstructRef ((kn, i), 2) in
    ( ctor_struct_name_of_ref nil_ref,
      ctor_struct_name_of_ref cons_ref )
  | _ -> ("Nil", "Cons")

(** Whether a C++ type is an erased placeholder. *)
let is_cpp_dummy_type : Cpp_ir.Lowered.Type.t -> bool = function Erased _ -> true | _ -> false

(** The type under any module or namespace qualification.  Questions about
    what a type {i is} -- which inductive, at which instantiation -- are about
    the type inside the qualification, not the wrapper. *)
let rec unqualify_ty : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Const t | In_namespace (_, t) -> unqualify_ty t
  | t -> t

(** How a value is represented in the slot it is built into.  [Native]: at its
    own type.  [Boxed]: inside a [std::any], so it must take the canonical
    erased shape every producer of its Rocq type agrees on, which the fixed
    [any_cast] reading it back expects; and the {!box_kind} says how deep
    that shape goes. *)
type slot_repr = Native | Boxed of box_kind

(** What a boxed slot stands for.  [Var_box]: a type variable -- an erased
    field, an existential's payload -- read at whatever type its consumer
    knows.  [Family_box]: a value-indexed family ([den t]), whose generic
    consumers read every level boxed in turn, a list's elements included. *)
and box_kind = Var_box | Family_box

(** [names_erased_alias t] -- [t] names a type-level declaration whose body
    erased, spelled through its alias [using memCType = std::any]: a
    type-level function of a value ([memCType c]), or a class field with no
    instance behind it. *)
let names_erased_alias : Cpp_ir.Lowered.Type.t -> bool = function
  | Entity_application (g, _, _) -> Table.is_erased_type_const g
  | _ -> false

let is_fully_erased_fun_ty : Cpp_ir.Lowered.Type.t -> bool = function
  | Function (dom, cod) ->
    dom <> [] && List.for_all Cpp_ir.Types.prints_as_any dom && Cpp_ir.Types.prints_as_any cod
  | _ -> false

(** [partially_erased_fun_ty t] -- true of a function type that erased only its
    arguments and kept a concrete result, as
    [std::function<uint64_t(std::any)>] has.  A closure landing in such a slot
    was written at the concrete domain, so it reaches the slot through the
    [crane_erase_fn] adapter -- taken at the slot's own result type, since
    erasing that too would box the result twice. *)
let partially_erased_fun_ty : Cpp_ir.Lowered.Type.t -> bool = function
  | Function (dom, cod) ->
    let erased t = Cpp_ir.Types.prints_as_any t || names_erased_alias t in
    List.exists erased dom && not (Cpp_ir.Types.prints_as_any cod)
  | _ -> false

(** [erased_domain_fun_ty t] -- true of a function type that erased at least one
    of its arguments, whichever way its result went.  This is the condition
    under which a closure written at the concrete domain needs the
    [crane_erase_fn] adapter: nothing converts to such a signature on its own.

    Strictly weaker than {!partially_erased_fun_ty}, and neither implies nor is
    implied by {!is_fully_erased_fun_ty}. *)
let erased_domain_fun_ty : Cpp_ir.Lowered.Type.t -> bool = function
  | Function (dom, _) ->
    List.exists (fun t -> Cpp_ir.Types.prints_as_any t || names_erased_alias t) dom
  | _ -> false

(** [is_boxed_type t] — true if a value of type [t] is known to be physically
    inside a [std::any], and may therefore be boxed into and [any_cast] out of.
    Deliberately narrower than {!Cpp_ir.Types.prints_as_any}: an opaque type
    ({!Representation_obligation.Opaque_type}) spells itself [std::any] but
    makes no claim about the representation, so it is
    excluded. *)
let is_boxed_type : Cpp_ir.Lowered.Type.t -> bool = function Any | Erased _ -> true | _ -> false


(** [materialise_opaque ty] — replace every opaque type
    ({!Representation_obligation.Opaque_type}) in [ty] with [Any].

    Apply this wherever [ty] is about to be {e written down} — a field, a
    parameter, a return type, a template argument in the generated header.
    An opaque type means "we do not know the representation", but spelling
    [std::any] in a declaration is precisely what decides it: from that point
    on the value really is boxed, and downstream code is entitled to box into
    and [any_cast] out of the slot.  An opaque type therefore survives only in the
    inferred type of an expression, never in a declaration. *)
let materialise_opaque (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  Cpp_ir.Types.map (function Obligation Opaque_type -> Any | t -> t) ty

(** [is_all_erased t] — true iff [t] is directly erased OR all of its type
    arguments are recursively all-erased.  Ground types without arguments
    (e.g. [nat], [bool]) return false.  Examples:
    - [pair<any, any>] → true (both args erased)
    - [pair<any, pair<any, any>>] → true (nested, all leaves erased)
    - [pair<any, List<any>>] → true ([List<any>] has all-erased args)
    - [pair<uint64_t, any>] → false ([uint64_t] is concrete)
    Used to detect fully-erased tuple chains where the runtime encoding
    stores [pair<any,any>] at every level regardless of the static type. *)
let rec is_all_erased : Cpp_ir.Lowered.Type.t -> bool = function
  | ty when Cpp_ir.Types.prints_as_any ty -> true
  | Entity_application (_, args, _) when args <> [] -> List.for_all is_all_erased args
  | _ -> false

(** [extract_template_args ty] — unwrap namespace and shared_ptr wrappers
    to extract the template arguments from the innermost
    [Entity_application].  Returns [\[\]] if there is none.

    For example, [In_namespace (ns, Entity_application (g, \[T1; T2\], _))]
    returns [\[T1; T2\]]. *)
let rec extract_template_args : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t list = function
  | Entity_application (_, args, _) -> args
  | In_namespace (_, inner) -> extract_template_args inner
  | Shared_pointer inner -> extract_template_args inner
  | _ -> []

(** [is_core_erased_ty ty] — true if [ty] represents an erased position in the
    Core term: a bare type variable, [Core.Type.Unknown], an empty [Core.Type.Meta] or a [Core.Type.Open]
    hole, seen through filled [Core.Type.Meta]s.  These
    arise from type-level parameters that were erased during extraction
    and correspond to [std::any] in the C++ representation. *)
and is_core_erased_ty = function
  | Core.Type.Variable _ | Core.Type.Unknown -> true
  | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
  | Core.Type.Meta {contents = Some t} -> is_core_erased_ty t
  | _ -> false

(** Check if a C++ type is a skipped type (inline custom with empty string).
    Such types arise from [Crane Extract Skip] and represent infrastructure
    (e.g. ReSum) that should be completely erased. *)
let is_skipped_cpp_type : Cpp_ir.Lowered.Type.t -> bool = function
  | Entity_application (r, _, _) -> Table.is_inline_custom r && Table.find_custom_opt r = Some ""
  | _ -> false

(** Whether a C++ type is a type class's, under [const], a reference or a
    [shared_ptr]. *)
let rec is_typeclass_type_cpp : Cpp_ir.Lowered.Type.t -> bool = function
  | Entity_application (r, _, _) -> Table.is_typeclass r
  | Const t | Reference ((Lvalue | Forwarding), t) | Shared_pointer t -> is_typeclass_type_cpp t
  | _ -> false

(** Check if a Core type is a skipped type (inline custom with empty string).
    Same semantics as [is_skipped_cpp_type] but operates on Core.
    Used to filter out parameters whose type was [Crane Extract Skip]-ped
    (e.g. [ReSum]-typed typeclass parameters from the ITree library). *)
let is_skipped_core_type = function
  | Core.Type.Global_app {head = r; _} ->
    Table.is_inline_custom r && Table.find_custom_opt r = Some ""
  | _ -> false

(** Check if a Core type contains any unresolved type variable or placeholder.
    Returns true for Core.Type.Variable, unresolved Core.Type.Meta, and Core.Type.Unknown. Used to
    guard Core.Type.Variable substitution: we only substitute with fully concrete types. *)
let rec has_tvar = function
  | Core.Type.Variable _ -> true
  | Core.Type.Unknown -> true
  | Core.Type.Arrow {parameter = t1; result = t2} -> has_tvar t1 || has_tvar t2
  | Core.Type.Global_app {type_arguments = args; _} -> List.exists has_tvar args
  | Core.Type.Meta {contents = Some t} -> has_tvar t
  | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
  | _ -> false

(** Apply a type-level transformation to every type annotation in a Core term. *)
let rec map_types_in_ast (f : _ Core.Type.at -> _ Core.Type.at) = function
  | Core.Expr.Lambda {parameter = id; parameter_type = ty; body} ->
    Core.Expr.Lambda {parameter = id; parameter_type = f ty; body = map_types_in_ast f body}
  | Core.Expr.Let {binder = id; binder_type = ty; value = a; body = b; occurrence = occ} ->
    Core.Expr.Let {binder = id;
                   binder_type = f ty;
                   value = map_types_in_ast f a;
                   body = map_types_in_ast f b;
                   occurrence = occ}
  | Core.Expr.Global use -> Core.Expr.Global (Core.Global_use.map_types f use)
  | Core.Expr.Construct {result_type = ty; constructor = r; arguments = args; occurrence = occ} ->
    Core.Expr.Construct {result_type = f ty;
                         constructor = r;
                         arguments = List.map (map_types_in_ast f) args;
                         occurrence = occ}
  | Core.Expr.Match {scrutinee_type = ty; scrutinee = e; branches = brs; occurrence = occ} ->
    Core.Expr.Match {scrutinee_type = f ty; scrutinee = map_types_in_ast f e; branches = Array.map
          (fun {Core.Match.Branch.binders = ids; result_type = ty; pattern = pat; body = body} ->
            { Core.Match.Branch.binders = List.map (fun (id, t) -> (id, f t)) ids;
              result_type = f ty;
              pattern = pat;
              body = map_types_in_ast f body } )
          brs; occurrence = occ}
  | Core.Expr.Fixpoint g -> Core.Expr.Fixpoint (Core.Recursion.Group.map f (map_types_in_ast f) g)
  | Core.Expr.Cofixpoint g -> Core.Expr.Cofixpoint (Core.Recursion.Group.map f (map_types_in_ast f) g)
  | Core.Expr.Apply {callee = fn; arguments = args} ->
    Core.Expr.Apply {callee = map_types_in_ast f fn; arguments = List.map (map_types_in_ast f) args}
  | Core.Expr.Coerce {source_type = from; target_type = into; value = a; occurrence = mocc} ->
    Core.Expr.Coerce {source_type = f from; target_type = f into; value = map_types_in_ast f a; occurrence = mocc}
  | Core.Expr.Boxed_value {value = a; occurrence = mocc} ->
    Core.Expr.Boxed_value {value = map_types_in_ast f a; occurrence = mocc}
  | Core.Expr.Lambda_group_barrier {value = a; occurrence = mocc} ->
    Core.Expr.Lambda_group_barrier {value = map_types_in_ast f a; occurrence = mocc}
  | Core.Expr.Persistent_array {elements = arr; default = def} ->
    Core.Expr.Persistent_array {elements = Array.map (map_types_in_ast f) arr; default = map_types_in_ast f def}
  | Core.Expr.Tuple args -> Core.Expr.Tuple (List.map (map_types_in_ast f) args)
  | ( Core.Expr.Bound_variable _
    | Core.Expr.Runtime_error _
    | Core.Expr.Erased_value _
    | Core.Expr.Axiom_value _
    | Core.Expr.UInt63 _ | Core.Expr.Numeral _
    | Core.Expr.Float64 _
    | Core.Expr.String _ ) as t -> t

(** Apply a Core.Type.Variable substitution to a Core type. *)
let rec subst_tvars_type subst = function
  | Core.Type.Variable {variable = i; _} ->
    ( match List.assoc_opt i subst with
    | Some t -> t
    | None -> Core.Type.Variable {rigidity = Core.Type.Rigidity.Schematic; variable = i} )
  | Core.Type.Arrow {parameter = a; result = b} ->
    Core.Type.Arrow {parameter = subst_tvars_type subst a; result = subst_tvars_type subst b}
  | Core.Type.Global_app {head = r; type_arguments = args; index_arguments = a} ->
    Core.Type.Global_app {head = r; type_arguments = List.map (subst_tvars_type subst) args; index_arguments = a}
  | Core.Type.Meta {contents = Some t} -> subst_tvars_type subst t
  | Core.Type.Variable_app {head = i; arguments = args} ->
    (* The head of an application is a type variable too, but only another
       variable can stand in that position, so a mapping to a structured type
       leaves it alone. *)
    let i =
      match List.assoc_opt i subst with
      | Some (Core.Type.Variable {variable = j; _}) -> j
      | _ -> i
    in
    Core.Type.Variable_app {head = i; arguments = List.map (subst_tvars_type subst) args}
  | t -> t

(** Replace every unnamed [Variable] with [Any] (for type erasure in indexed
    inductives). Used when a type has variables that don't correspond to any
    template parameters.  Named variables are kept. *)
let tvar_erase_type =
  Cpp_ir.Types.rewrite (fun (t : Cpp_ir.Lowered.Type.t) ->
      match t with
      | Variable (Index (_, None)) -> Some Any
      | Variable (Index (_, Some _) | Named _) as ty -> Some ty
      | _ -> None )

(** Erase a type argument down to its outermost applied type constructors,
    boxing every leaf: [List<Nat>] becomes [List<std::any>] and a bare [Nat]
    becomes [std::any].

    This is the erasure required wherever one C++ type has to serve every
    instantiation of an existential -- an index-position argument of an
    indexed inductive (after an index erased as
    [Core.Type.Erased Core.Erasure_reason.Type_argument]), or a value
    flowing into an erased slot.  Collapsing the whole argument to [std::any]
    would also be uniform, but it throws away a structure the consumer needs:
    the payload of a [{ T : Type & list T }] is still a list, and only its
    element type is existential.

    A leaf is collapsed rather than recursed into so that a namespaced
    [Entity_application] like [Nat] yields plain [std::any], not the malformed
    [typename Nat::std::any]. *)
let rec index_erase_type (ty : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t =
  match ty with
  | Entity_application (r, (_ :: _ as tys), args) -> Entity_application (r, List.map index_erase_type tys, args)
  | Named (id, (_ :: _ as tys)) -> Named (id, List.map index_erase_type tys)
  | External (id, (_ :: _ as tys)) -> External (id, List.map index_erase_type tys)
  | Non_deduced t -> Non_deduced (index_erase_type t)
  | Rebind (h, x) -> Rebind (index_erase_type h, index_erase_type x)
  | In_namespace (r, inner) -> (
    match index_erase_type inner with
    | Any -> Any
    | t -> In_namespace (r, t) )
  | _ -> Any

(** Extract the return type from a Core function type, stripping every
    [Core.Type.Arrow] layer. *)
let rec core_return_type = function
  | Core.Type.Arrow {result = rest; _} -> core_return_type rest
  | t -> t

(** Whether a global has no C++ spelling: whatever mapped it mapped it to the
    empty string.  [sum1] is one -- an event family that is a sum is still
    erased, and there is nothing to write where it would go. *)
let ref_has_no_spelling r = Table.find_custom_opt r = Some ""

(** Whether a global was skipped -- [Crane Extract Skip] records it as an
    inline custom whose C++ text is empty.  Skipped globals are
    infrastructure, and nothing of them survives into C++. *)
let ref_is_skipped r = Table.is_inline_custom r && ref_has_no_spelling r

(** Whether [r] has no C++ name to be written as.

    Two ways that happens, and they have to be asked together because both
    produce text no compiler will take.  A global mapped to the empty string --
    what [Crane Extract Skip] records -- vanishes, so a type applied to it
    renders as a bare argument list, [<typename I::PROV>].  A global from a
    module [Crane Extract Skip Module] left out renders as the name it would
    have had, [IO_axioms::ioE], which nothing in the file introduces -- unless
    it is mapped itself, as [R] is to [Real] in the skipped
    [RbaseSymbolsImpl]: its mapping is its name. *)
let ref_has_no_cpp_name r =
  let rec mp_skipped mp =
    is_skip_module mp
    || match mp with MPdot (parent, _) -> mp_skipped parent | _ -> false
  in
  match Table.find_custom_opt r with
  | Some s -> String.equal s ""
  | None -> mp_skipped (modpath_of_r r)

(** Whether [ty] mentions anywhere a global with no C++ name.

    Asked of the type {e as the printer will write it}, not as it stands: an
    application of a nameless constructor comes out as its arguments, so the
    constructor having no name of its own costs the type nothing, and asking
    before stripping it would condemn a type that prints perfectly well.  That
    is not hypothetical -- it is every reified [Vis] whose event type is a
    projection through a dictionary, and answering "no name" there gives up a
    spelling the generator had.

    Asked before writing a type into a position that has an alternative to
    writing it. *)
let has_no_cpp_spelling (ty : Cpp_ir.Lowered.Type.t) =
  let as_printed =
    Cpp_ir.Types.map
      (fun (t : Cpp_ir.Lowered.Type.t) ->
        match t with
        | Apply (Entity_application (r, _, _), [arg]) when ref_has_no_cpp_name r -> arg
        | t -> t )
      ty
  in
  Cpp_ir.Types.exists
    (fun (t : Cpp_ir.Lowered.Type.t) -> match t with Entity_application (r, _, _) -> ref_has_no_cpp_name r | _ -> false)
    as_printed

(** Whether a Core type's result is a skipped type -- a [ReSum] instance, say,
    whose class extraction records as a [ConstRef] mapped to the empty string,
    so {!Table.is_typeclass_type} does not recognise it.  Values of such a type
    are infrastructure and are erased. *)
let core_ret_is_skipped ty =
  match core_return_type ty with
  | Core.Type.Global_app {head = rr; _} -> ref_is_skipped rr
  | _ -> false

(** Whether a value of Core type [ty] is a typeclass instance.

    The result is what decides it: an instance parameterised over types is
    still an instance, and its type is an arrow -- [MList : forall A, Monoid
    (list A)].  This is the one place that answer is worked out. *)
let core_type_is_instance ty =
  Table.is_typeclass_type (core_return_type ty) || core_ret_is_skipped ty

(** Extract argument types and return type from a function type. *)
let rec get_args_and_ret acc = function
  | Core.Type.Arrow {parameter = t; result = rest} -> get_args_and_ret (t :: acc) rest
  | ret_ty -> (List.rev acc, ret_ty)

(** Strip [n] non-dummy arrow levels from a Core type, resolving Core.Type.Meta
    indirections and automatically skipping erased (Core.Type.Erased) arrows.
    Returns the codomain after stripping, or [None] if the type has fewer
    than [n] non-dummy arrow levels. *)
let rec strip_arrows_n n ty =
  if n <= 0 then Some ty
  else match resolve_meta ty with
    | Core.Type.Arrow {parameter = t1; result = rest} when Core_util.is_erased_type t1 ->
      (* Skip erased type-param arrow without consuming a real argument *)
      strip_arrows_n n rest
    | Core.Type.Arrow {result = rest; _} -> strip_arrows_n (n - 1) rest
    | _ -> None

(** Strip one level of reference or const-qualification from a C++ type.
    Normalises lambda parameter types before building [Function] types.
    Unlike [Control_to_cpp.Tail.strip_ref_and_const_type] this is intentionally
    non-recursive: a forwarding reference [T&&] becomes [T&]. *)
let strip_cpp_ref_const : Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t = function
  | Reference (Lvalue, t) | Const t -> t
  | Reference (Forwarding, t) -> Reference (Lvalue, t)
  | t -> t

(** Count non-erased arguments in a Core application.
    [Core.Expr.Erased_value] nodes represent erased type/proof parameters that are not
    passed to C++ functions; this returns the count of the remaining actual
    value arguments. *)
let count_real_core_args args =
  List.length (List.filter (fun a ->
    match a with Core.Expr.Erased_value _ -> false | _ -> true) args)

(** Whether copying a value of this C++ type is free.

    A type declared with [Crane TriviallyCopyable] qualifies only when its
    type arguments do -- copying a [std::pair] costs what copying its
    components costs. *)
let rec is_trivially_copyable_type (t : Cpp_ir.Lowered.Type.t) =
  match t with
  (* A typed-mapped type: its copy model ({!Mapping_plan.copies_cheaply}). *)
  | Entity_application (g, ts, _) when Mapping_plan.is_type_head g ->
    Mapping_plan.copies_cheaply (Mapping_plan.find g) ~argument:(fun i ->
        match List.nth_opt ts i with Some t -> is_trivially_copyable_type t | None -> false)
  | Entity_application (g, ts, _) ->
    is_enum_inductive g || Table.is_custom_scalar_ref g
    || Table.is_trivially_copyable_ref g
       && List.for_all is_trivially_copyable_type ts
  | In_namespace (g, _) -> is_enum_inductive g || Table.is_custom_scalar_ref g
  | _ -> false

(** Whether copying a value of Core type [ty] is free: {!is_trivially_copyable_type}
    read off the Core type. *)
let rec core_is_trivially_copyable ty =
  match resolve_meta ty with
  | Core.Type.Global_app {head = g; type_arguments = args; _} when Mapping_plan.is_type_head g ->
    Mapping_plan.copies_cheaply (Mapping_plan.find g) ~argument:(fun i ->
        match List.nth_opt args i with Some t -> core_is_trivially_copyable t | None -> false)
  | Core.Type.Global_app {head = g; type_arguments = args; _} ->
    is_enum_inductive g || Table.is_custom_scalar_ref g
    || Table.is_trivially_copyable_ref g && List.for_all core_is_trivially_copyable args
  | _ -> false

let boxes_field ty =
  Table.boxed_fields ()
  &&
  match resolve_meta ty with
  | Core.Type.Global_app {head = (GlobRef.IndRef _ as g); _} ->
    (not (Table.is_coinductive g)) && not (core_is_trivially_copyable ty)
  | _ -> false

let boxes_param_field ~owner ty =
  Table.boxed_fields ()
  && (not (Table.is_shared_variant owner))
  && match resolve_meta ty with Core.Type.Variable _ -> true | _ -> false

module Ctor_fields = struct
  type t = {
    inductive : GlobRef.t;
    types : Core.Type.t list;
  }

  let of_ctor cname =
    let inductive =
      match cname with GlobRef.ConstructRef (ind, _) -> GlobRef.IndRef ind | r -> r
    in
    let types =
      List.filter (fun t -> not (is_erased_type t)) (Option.default [] (Table.get_ctor_ip_types_opt cname))
    in
    {inductive; types}

  let field f i p = match List.nth_opt f.types i with Some ty -> p ty | None -> false

  let is_self_or_mutual f r =
    globref_equal r f.inductive
    ||
    match (r, f.inductive) with
    | GlobRef.IndRef (kn2, _), GlobRef.IndRef (kn, _) -> MutInd.CanOrd.equal kn2 kn
    | _ -> false

  let rec mentions_self f = function
    | Core.Type.Global_app {head = r; type_arguments = args; _} ->
      is_self_or_mutual f r || List.exists (mentions_self f) args
    | Core.Type.Meta {contents = Some t} -> mentions_self f t
    | Core.Type.Arrow {parameter = t1; result = t2} -> mentions_self f t1 || mentions_self f t2
    | _ -> false

  let self_or_mutual_ref f i =
    field f i (function
      | Core.Type.Global_app {head = r; _} | Core.Type.Meta {contents = Some (Core.Type.Global_app {head = r; _})} ->
        is_self_or_mutual f r
      | _ -> false )

  let nested_self_ref f i =
    field f i (function
      | Core.Type.Global_app {head = r;
                              type_arguments = args; _}
                                | Core.Type.Meta {contents = Some (Core.Type.Global_app {head = r;
                                                                                          type_arguments = args; _})}
        when not (is_self_or_mutual f r) ->
        List.exists (mentions_self f) args
      | _ -> false )

  (* A field recurses THROUGH a boxed-element container (e.g. [list <self>] ->
     [immer::flex_vector<immer::box<self>>]) when the container carries a
     [Boxed Element] wrapper and a self/mutual ref appears in its type args.
     The element box breaks the completeness cycle, so such a field is stored
     by VALUE (matching the declaration, {!Core_to_cpp.Lower_decl}) -- it is not
    shared_ptr-wrapped and must not
     be dereferenced when bound in a match arm. *)
  let recurses_through_boxed f i =
    let rec go = function
      | Core.Type.Global_app {head = g; type_arguments = args; _} -> (
        match Table.find_boxed_wrapper_opt g with
        | Some _ when List.exists (mentions_self f) args -> true
        | _ -> List.exists go args )
      | Core.Type.Meta {contents = Some t'} -> go t'
      | Core.Type.Arrow {parameter = a; result = b} -> go a || go b
      | _ -> false
    in
    field f i go

  let boxed f i = field f i boxes_field

  let param_boxed f i = field f i (boxes_param_field ~owner:f.inductive)

  let behind_pointer f i =
    (not (Table.is_coinductive f.inductive))
    && ( (not (recurses_through_boxed f i)) && (self_or_mutual_ref f i || nested_self_ref f i)
       || boxed f i || param_boxed f i )
end

let is_prod_core_type ty =
  match resolve_meta ty with
  | Core.Type.Global_app {head = r; _} -> is_prod_global r
  | _ -> false

(* Rocq BinNums.positive constructor indices (1-based): xI = 2n+1, xO = 2n, xH = 1 *)
let positive_xI_idx = 1
let positive_xO_idx = 2
let positive_xH_idx = 3

(* Rocq BinNums.Z constructor indices (1-based): Z0, Zpos, Zneg *)
let z_pos_idx = 2
let z_neg_idx = 3

(* Rocq Decimal/Hexadecimal.uint constructor indices (1-based):
   Nil = 1; digits D0..D9 = 2..11 (decimal), D0..Df = 2..17 (hex) *)
let uint_nil_idx        = 1
let decimal_d0_idx      = 2
let decimal_d9_idx      = 11
let hex_d0_idx          = 2
let hex_df_idx          = 17

(* Rocq Number.uint constructor indices (1-based): UIntDecimal, UIntHexadecimal *)
let num_uint_decimal_idx = 1
let num_uint_hex_idx     = 2

(* Rocq Decimal.signed_int / Hexadecimal.signed_int constructor indices (1-based):
   Pos, Neg *)
let signed_pos_idx = 1
let signed_neg_idx = 2

(** {2 Template-parameter shape of a C++ signature}

    These live here rather than in {!Core_plan.Plan_templates} because both the declaration
    emitter and the call emitter need them: the first to decide which template
    parameters a signature can leave to deduction, the second to supply the
    ones it cannot. *)

module IntSet = Core_util.IntSet

(** The type arguments a custom template writes: the indices of its type
    holes, [%t{i}] and [%elem{i}] alike ({!Cpp_ir.Foreign_template.type_template}).
    E.g. ["std::shared_ptr<ITree<%t1>>"] gives [{1}], and
    ["crane::list<%elem>"] [{0}]. *)
let template_referenced_positions template_str =
  List.fold_left
    (fun acc -> function
      | Cpp_ir.Foreign_template.Ty_arg i | Cpp_ir.Foreign_template.Elem i -> IntSet.add i acc
      | _ -> acc )
    IntSet.empty
    (Cpp_ir.Foreign_template.type_template template_str)

(** For a custom/monad GlobRef, return the set of type-arg positions that
    appear in its template string.  Returns [None] if no custom template
    exists or the template is empty (all positions are implicitly
    referenced). *)
let custom_referenced_positions_opt g =
  let check_template = function
    | Some s when s <> "" -> Some (template_referenced_positions s)
    | _ -> None
  in
  match check_template (Table.get_monad_template_opt g) with
  | Some _ as r -> r
  | None -> check_template (Table.find_custom_opt g)

(** [written_type_args g tys] keeps only those of [g]'s type arguments that a
    spelling of [g] actually writes.

    A custom template writes the [%tN] it names and no others -- the reified
    [ITree] carries its event family in the node rather than in the type, and
    writes only the result -- and a Crane-generated declaration says the same
    about a position it declared phantom.  What stands in an unwritten position
    is not in the rendered type at all, so nothing there is deducible, erased,
    or otherwise visible to C++. *)
let type_arg_is_written g =
  match custom_referenced_positions_opt g with
  | Some referenced -> fun i -> IntSet.mem i referenced
  | None -> fun i -> not (Table.is_phantom_type_param g i)

let written_type_args g tys =
  List.filteri (fun i _ -> type_arg_is_written g i) tys

(** Replace every unwritten type argument (see {!written_type_args}) by
    [Void], so a predicate over the result reads the type as it is spelled. *)
let prune_unwritten_args =
  Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
      match t with
      | Entity_application (g, tys, es) ->
        let written = type_arg_is_written g in
        Entity_application (g, List.mapi (fun i t -> if written i then t else (Void : Cpp_ir.Lowered.Type.t)) tys, es)
      | t -> t )

(** Whether a single type node erases to [std::any]: [Any] and the opaque
    obligation themselves, and an unnamed variable, which
    {!tvar_erase_type} turns into one. *)
let is_tany_node (t : Cpp_ir.Lowered.Type.t) =
  match t with
  | Any | Obligation Opaque_type | Variable (Index (_, None)) -> true
  | _ -> false

(** Like [has_tany_in_type] but also treats the [Erased] markers (type,
    proof, implicit) as erased types.  Used for non-lambda let bindings where
    [auto] is the right fallback -- but NOT for a [Function]-typed lambda,
    where we want to preserve the lambda's concrete return type. *)
let has_erased_type_in_type =
  Cpp_ir.Types.exists (fun t -> is_tany_node t || is_cpp_dummy_type t)

(** Whether a C++ type contains [std::any] anywhere.  Used to detect a
    let-binding whose type annotation still holds unresolved carrier
    projections, to be replaced by concrete types from the generated lambda. *)
let has_tany_in_type = Cpp_ir.Children.exists_type is_tany_node

let has_tany_written t = has_tany_in_type (prune_unwritten_args t)

let rec type_is_erased (ty : Cpp_ir.Lowered.Type.t) : bool =
  match ty with
  | Const inner | In_namespace (_, inner) -> type_is_erased inner
  | t -> is_tany_node t

(** Check if a C++ type contains an unnamed type variable
    ([Variable (Index (_, None))]).  Used to detect types that can't be fully
    resolved in monomorphized contexts (tvars=[]), where a nested unnamed
    variable would print as invalid C++ like
    List<T1>. *)
let has_unnamed_tvar =
  Cpp_ir.Children.exists_type (fun (t : Cpp_ir.Lowered.Type.t) ->
      match t with Variable (Index (_, None)) -> true | _ -> false )

(** Every unresolved type variable replaced with [Any]. *)
let resolve_tvars_to_any =
  Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
      match t with Variable (Index (_, None)) -> Any | t -> t )

(** Filter erased type arguments from a template argument list, each argument
    paired with a key that survives with it, using a two-phase approach:
    proof erasure stripping followed by all-or-nothing type erasure.

    Phase 1: Strip proof-erasure markers ([Erased Proof], from
    [Core.Type.Erased Core.Erasure_reason.Proof]).
    These are positional placeholders in Core that have no C++ analog.
    They must be removed before checking for erased types, otherwise their
    presence would trigger full erasure of concrete type arguments.

    Phase 2: Apply the "all or nothing" rule for erased types.
    If ANY remaining type argument prints as [std::any] ({!Cpp_ir.Types.prints_as_any}:
    [Any], an opaque type, or an [Erased Type] / [Erased Implicit] marker), drop ALL
    type arguments and return [[]].  With [~preserve_positions:true] nothing
    is dropped: each such argument is written [Any] in its place instead.

    The "all or nothing" rule is required because C++ template arguments are
    positional. If we kept some type args and dropped others, the remaining
    args would shift into the wrong parameter positions, causing type mismatches.

    Dropping all args is safe because C++ template argument deduction can
    infer type arguments from value arguments at the call site. For example:
    - [std::make_optional(5u)] deduces [std::optional<unsigned int>]
    - [std::vector v{1, 2, 3}] deduces [std::vector<int>]

    It is called wherever a call writes a global's explicit type arguments
    ([Core_to_cpp.Lower_expr], [Core_to_cpp.Calls]).

    Example scenarios (keys omitted):

    1. Concrete types (no erasure):
       Input: [[nat; bool]]
       Output: [[nat; bool]]

    2. Proof in middle (strip but keep others):
       Input: [[nat; Erased Proof; bool]]
       After phase 1: [[nat; bool]]
       Output: [[nat; bool]]

    3. Erased type in middle (drop all):
       Input: [[nat; Erased Type; bool]]
       After phase 1: [[nat; Erased Type; bool]]
       After phase 2: [[]] (erased)

    4. Only proofs (drop all):
       Input: [[Erased Proof; Erased Proof]]
       After phase 1: [[]]
       Output: [[]]

    @param pairs  keyed C++ types (template arguments)
    @return the filtered list: either all concrete types or empty, unless
      [preserve_positions] *)
let filter_erased_keyed ?(preserve_positions = false) (pairs : ('k * Cpp_ir.Lowered.Type.t) list) =
  let all = pairs in
  let pairs =
    List.filter (fun (_, (t : Cpp_ir.Lowered.Type.t)) -> match t with Erased Proof -> false | _ -> true) pairs
  in
  if List.length pairs <> List.length all then
    Probe.hit "REPAIR_filter_erased_type_args_prop" (fun () -> "");
  if preserve_positions then
    List.map (fun (k, t) -> (k, if Cpp_ir.Types.prints_as_any t then (Any : Cpp_ir.Lowered.Type.t) else t)) pairs
  else if List.exists (fun (_, t) -> Cpp_ir.Types.prints_as_any t) pairs then (
    Probe.hit "REPAIR_filter_erased_type_args_drop" (fun () -> "");
    [] )
  else pairs

let filter_erased_type_args ?preserve_positions tys =
  List.map snd (filter_erased_keyed ?preserve_positions (List.map (fun t -> ((), t)) tys))

(** [refine_erased_by ~expected actual] takes, at every position where
    [actual] erased and [expected] did not, the spelling [expected] gives.

    A producer computes a type from its own instantiation, which knows nothing
    of the positions the value is going to occupy; the slot the value flows
    into has already written the type down.  Where the two disagree only in how
    much they erased, the slot's spelling is the one both producers for that
    slot will agree on, and the one the declaration states -- so it wins, and
    the producer's concrete knowledge is kept everywhere else.

    Only erasure is refined: a position where both are concrete keeps the
    producer's, and a shape mismatch is left alone entirely. *)
let rec refine_erased_by ~(expected : Cpp_ir.Lowered.Type.t) (actual : Cpp_ir.Lowered.Type.t) :
    Cpp_ir.Lowered.Type.t =
  let erased t = Cpp_ir.Types.prints_as_any t in
  if erased actual && not (erased expected) then expected
  else
    let go e a = refine_erased_by ~expected:e a in
    match (expected, actual) with
    | Entity_application (g, ea, _), Entity_application (g', aa, x)
      when globref_equal g g' && List.length ea = List.length aa ->
      Entity_application (g', List.map2 go ea aa, x)
    | Function (ed, ec), Function (ad, ac) when List.length ed = List.length ad ->
      Function (List.map2 go ed ad, go ec ac)
    | Const e, Const a -> Const (go e a)
    | Reference (ke, e), Reference (ka, a) when ke = ka -> Reference (ka, go e a)
    | Pointer e, Pointer a -> Pointer (go e a)
    | Shared_pointer e, Shared_pointer a -> Shared_pointer (go e a)
    | _, In_namespace (ns, a) -> In_namespace (ns, refine_erased_by ~expected a)
    | In_namespace (_, e), _ -> refine_erased_by ~expected:e actual
    | _ -> actual

(* What [fills] filled the hole [o] with, if anything. *)
let filled_with fills o =
  List.find_map (fun (o', t) -> if Core.Open.equal o o' then Some t else None) fills

let refine_erased ?(fills = ref []) ~writable have want =
  let erased = function
    | Core.Type.Unknown | Core.Type.Erased _ | Core.Type.Meta {contents = None} | Core.Type.Open _ -> true
    | _ -> false
  in
  let filled = function
    | Core.Type.Open o as t -> Option.default t (filled_with !fills o)
    | t -> t
  in
  let rec refine have want =
    match (filled (resolve_meta have), resolve_meta want) with
    | Core.Type.Open o, w when (not (erased w)) && writable w ->
      fills := (o, w) :: !fills;
      w
    | h, w when erased h -> if (not (erased w)) && writable w then w else h
    | Core.Type.Global_app {head = n;
                            type_arguments = ha;
                            index_arguments = sc}, Core.Type.Global_app {head = m; type_arguments = wa; _}
      when GlobRef.CanOrd.equal n m && List.length ha = List.length wa ->
      Core.Type.Global_app {head = n; type_arguments = List.map2 refine ha wa; index_arguments = sc}
    | Core.Type.Arrow {parameter = a; result = b}, Core.Type.Arrow {parameter = c; result = d} ->
      Core.Type.Arrow {parameter = refine a c; result = refine b d}
    | h, _ -> h
  in
  refine have want

(* Rebuilt only where a hole is filled, so the rest is shared. *)
let rec fill_holes_type fills t =
  match t with
  | Core.Type.Open o -> Option.default t (filled_with fills o)
  | Core.Type.Meta {contents = Some u} ->
    let u' = fill_holes_type fills u in
    if u' == u then t else u'
  | Core.Type.Arrow {parameter = a; result = b} ->
    let a' = fill_holes_type fills a and b' = fill_holes_type fills b in
    if a' == a && b' == b then t else Core.Type.Arrow {parameter = a'; result = b'}
  | Core.Type.Global_app {head = g; type_arguments = ts; index_arguments = args} ->
    let ts' = List.map (fill_holes_type fills) ts in
    if List.for_all2 ( == ) ts ts' then t else Core.Type.Global_app {head = g;
                                                                     type_arguments = ts';
                                                                     index_arguments = args}
  | _ -> t

let fill_holes fills e =
  match fills with [] -> e | _ -> Core_util.ast_map_types (fill_holes_type fills) e

let refine_param_from_slot ~tvars ~slot (bare : Cpp_ir.Lowered.Type.t) =
  let name_of (t : Cpp_ir.Lowered.Type.t) =
    match t with
    | Variable (Index (_, Some n) | Named n) -> Some n
    | Variable (Index (i, None)) -> Some (Cpp_ir.Type.positional_id i)
    | _ -> None
  in
  let spelled_by_bare = Cpp_ir.Types.variable_names bare in
  let nameable n = List.exists (Id.equal n) tvars || Id.Set.mem n spelled_by_bare in
  let erased =
    Cpp_ir.Types.map
      (fun t -> match name_of t with Some n when not (nameable n) -> Cpp_ir.Type.Any | _ -> t)
      slot
  in
  let keeps_names = Id.Set.subset spelled_by_bare (Cpp_ir.Types.variable_names erased) in
  let says_something =
    let normalise =
      Cpp_ir.Types.map (fun (t : Cpp_ir.Lowered.Type.t) : Cpp_ir.Lowered.Type.t ->
          if is_tany_node t || is_cpp_dummy_type t then Any
          else match t with Variable (Index (_, Some n) | Named n) -> Variable (Named n) | t -> t )
    in
    normalise erased <> normalise bare
  in
  if says_something && keeps_names && has_erased_type_in_type bare && has_erased_type_in_type erased then erased
  else bare

(** Collect (index, name) pairs for every type variable of a C++ type, sorted by index; a
    variable known only by name stands at index [0], ahead of the others. *)
let get_tvars_indexed (t : Cpp_ir.Lowered.Type.t) =
  let get_name i n =
    match n with
    | None -> tvar_id i
    | Some n -> n
  in
  let rec aux l : Cpp_ir.Lowered.Type.t -> _ = function
    | Promoted_member _ ->
      (* Promoted type var marker from a Record-turned-Type_class.  These
         represent projected type members (e.g., [Obj] from [PreCategory])
         and must be resolved through typeclass instance access — not as
         standalone template parameters. *)
      l
    | Variable (Index (i, n)) ->
      if List.exists (fun (x, _) -> i == x) l then
        l
      else
        (i, get_name i n) :: l
    | Variable (Named n) ->
      if List.exists (fun (_, m) -> Id.equal n m) l then l else (0, n) :: l
    | Entity_application (_, tys, _) -> List.fold_left aux l tys
    | Function (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Const ty -> aux l ty
    | In_namespace (_, ty) -> aux l ty
    | Reference (_, ty) -> aux l ty
    | Variant (_, tys) -> List.fold_left aux l tys
    | Shared_pointer ty -> aux l ty
    | Apply (ty, tys) -> List.fold_left aux l (ty :: tys)
    (* A carrier abstraction names the variables its body does -- written
       through a holder, [crane_carrier_tch<T1>::template c]. *)
    | Type_constructor ty -> aux l ty
    | _ -> l
  in
  List.sort (fun (x, _) (y, _) -> Int.compare x y) (aux [] t)

(** Like [get_tvar_indices] but only collects tvars that will actually
    appear in the rendered C++ type.  For custom types with a template
    (e.g. [std::shared_ptr<ITree<%t1>>]), only type-arg positions
    referenced by the template are visited.  Unreferenced positions hold
    phantom tvars (e.g. E in [itree E R] where the template only uses
    [%t1] = R) that the C++ compiler cannot deduce. *)
let get_rendered_tvar_indices (t : Cpp_ir.Lowered.Type.t) =
  let rec aux l : Cpp_ir.Lowered.Type.t -> _ = function
    | Promoted_member _ -> l
    | Variable (Index (i, _)) ->
      if List.mem i l then l else i :: l
    | Entity_application (g, tys, _) ->
      List.fold_left aux l (written_type_args g tys)
    | Function (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Const ty -> aux l ty
    | In_namespace (_, ty) -> aux l ty
    | Reference (_, ty) -> aux l ty
    | Variant (_, tys) -> List.fold_left aux l tys
    | Shared_pointer ty -> aux l ty
    | Apply (ty, tys) -> List.fold_left aux l (ty :: tys)
    | _ -> l
  in
  aux [] t


(** The arity at which the {e rendered} type applies each type variable.

    Asked instead of the Core reading wherever a rendered type is available,
    because erasure happens between the two and they then disagree without
    either being wrong.  An event family is the case in point: [semantic_
    function := list ptr -> itree E nat] applies [E] in Core and spells it
    nowhere in C++, and an alias that merely {e forwards} [E] into that one
    still has the application in its expanded Core body.  Reading the arity
    there makes the forwarder [template <typename> class e] while the alias it
    hands it to declared [typename e], which is the mismatch.  What the
    rendered type does with the variable is what its users have to agree
    with. *)
let rendered_tvar_arities (t : Cpp_ir.Lowered.Type.t) =
  let arities = Hashtbl.create 4 in
  let rec aux : Cpp_ir.Lowered.Type.t -> unit = function
    | Apply (Variable (Index (i, _)), tys) ->
      Hashtbl.replace arities i (List.length tys);
      List.iter aux tys
    | Entity_application (g, tys, _) -> List.iter aux (written_type_args g tys)
    | Function (tys, ty) -> List.iter aux (ty :: tys)
    | Const ty | In_namespace (_, ty) | Reference (_, ty) | Shared_pointer ty -> aux ty
    | Variant (_, tys) -> List.iter aux tys
    | Apply (ty, tys) -> List.iter aux (ty :: tys)
    | _ -> ()
  in
  aux t;
  arities

(** The type variables' names, sorted by index. *)
let get_tvars t = List.map snd (get_tvars_indexed t)

(** The type variables' indices only, sorted. *)
let get_tvar_indices t = List.map fst (get_tvars_indexed t)

(** Collect tvar indices that are represented concretely in the generated C++
    signature.

    In addition to the codomain and non-function domain parameters, tvars from
    fully rendered function signatures are primary: the function emitter
    ([Core_to_cpp.Functions]) can represent those signatures with [is_invocable_r_v]
    constraints.  This matters for a
    type such as [(B -> C) -> (A -> B) -> A -> C], where [B] occurs only in
    function-typed parameters but is nevertheless a real part of both callable
    signatures.

    Used by the function emitter (to choose between an [is_invocable_r_v]
    constraint and plain [TTtypename]), by {!Core_plan.Plan_templates.phantom_aware_temps}
    (to choose whether a template parameter needs a [void] default) and by the
    call emitter ({!explicit_tvar_prefix}). *)
let primary_tvar_indices (dom : Cpp_ir.Lowered.Type.t list) cod =
  let add_rendered acc t =
    List.fold_left
      (fun acc i -> IntSet.add i acc)
      acc
      (get_rendered_tvar_indices t)
  in
  let concrete, clean_fun =
    List.fold_left
      (fun (concrete, clean_fun) (t : Cpp_ir.Lowered.Type.t) ->
        match t with
        | Function _ -> (concrete, add_rendered clean_fun t)
        | _ -> (add_rendered concrete t, clean_fun) )
      (add_rendered IntSet.empty cod, IntSet.empty)
      dom
  in
  IntSet.union concrete clean_fun

(** Collect tvar indices that appear in type INDEX positions of inductives
    in the Core type.  Type indices are stripped from the C++ type by
    {!Core_to_cpp.Types.cpp_ir_of_core_type} but may be needed in function bodies
    for [any_cast] when matching on type-indexed inductives with
    wholesale-erased fields.

    Only collects tvars from inductives where [get_ind_num_param_vars_opt]
    succeeds and the number of type args exceeds the parameter count
    (indicating genuine indices, not parameters). *)
let collect_core_type_index_tvars core_ty =
  let result = ref IntSet.empty in
  let rec collect_tvars = function
    | Core.Type.Variable {variable = i; _} ->
      result := IntSet.add i !result
    | Core.Type.Arrow {parameter = t1; result = t2} ->
      collect_tvars t1; collect_tvars t2
    | Core.Type.Global_app {type_arguments = ts; _} ->
      List.iter collect_tvars ts
    | Core.Type.Meta {contents = Some t} -> collect_tvars t
    | _ -> ()
  in
  let rec walk = function
    | Core.Type.Arrow {parameter = t1; result = t2} -> walk t1; walk t2
    | Core.Type.Global_app {head = g; type_arguments = ts; _} ->
      ( match g with
      | GlobRef.IndRef (kn, _) ->
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars when num_param_vars < List.length ts ->
          List.iteri (fun i t ->
            if i >= num_param_vars then collect_tvars t
          ) ts
        | _ -> () );
        List.iter walk ts
      | _ -> List.iter walk ts )
    | Core.Type.Meta {contents = Some t} -> walk t
    | _ -> ()
  in
  walk core_ty;
  !result

(** Every type variable index the Core type mentions, in any position.

    The C++ type is what decides which parameters a signature {e spells}, but
    not how many it {e has}: erasure can drop a variable from the rendered type
    while the body and the call sites still number their arguments by the Core
    type.  A declaration that omitted such a variable would leave the body
    naming something the head never bound. *)
let collect_core_tvars = Core_util.core_tvars

(** Arity of every type variable that [tys] applies to arguments, keyed by its
    1-based de Bruijn index.  A Rocq parameter of kind [Type -> Type] reaches
    Core as the head of a {!Core.Type.Variable_app}, and a plain [typename] cannot be
    applied: such a parameter is declared [template <typename> class], and an
    explicit argument for it is a bare template name rather than a type. *)
let applied_core_tvar_arities tys =
  let arities = Hashtbl.create 4 in
  let rec scan = function
    | Core.Type.Variable_app {head = i; arguments = args} ->
      Hashtbl.replace arities i (List.length args);
      List.iter scan args
    | Core.Type.Global_app {type_arguments = args; _} -> List.iter scan args
    | Core.Type.Arrow {parameter = a; result = b} -> scan a; scan b
    | Core.Type.Meta {contents = Some t} -> scan t
    | _ -> ()
  in
  List.iter scan tys;
  arities

(** The type variables a declaration of type [core_ty] relaxes out of its template
    head.

    {!Core_plan.Plan_templates.relax_applied_return} replaces a higher-kinded parameter that is
    only ever {e applied} in the parameter list with one fresh [typename] per
    application, deduced from the argument, and leaves the original a phantom
    defaulted to [void]. A call must then not write a template name there,
    because the position no longer takes one.

    Asked here of the Core type rather than read back from the declaration: a
    table the declaration emitter fills cannot be consulted at a call site, since emission
    interleaves with body generation. The two agree because the condition is a
    property of the type both are built from -- applied somewhere in the
    domains, and spelled nowhere unapplied and nowhere in the codomain. *)
let relaxed_applied_core_tvars core_ty =
  let doms = core_domains core_ty
  and ret = core_return_type core_ty in
  let applied = Hashtbl.create 4
  and bare = ref IntSet.empty in
  let rec scan = function
    (* A variable of kind [Type -> Type] handed over as a bare template name --
       as the argument of an alias, [Sub UBE E] -- is written applied to the
       alias's own placeholder. That is an occurrence the declaration has to
       keep the parameter for, not an application it can relax. *)
    | Core.Type.Variable_app {head = i; arguments = args}
      when args = []
           || List.exists
                (fun a ->
                  match resolve_meta a with
                  | Core.Type.Unknown -> true
                  | _ -> false )
                args -> bare := IntSet.add i !bare
    | Core.Type.Variable_app {head = i; arguments = args} ->
      Hashtbl.replace applied i ();
      List.iter scan args
    | Core.Type.Variable {variable = i; _} -> bare := IntSet.add i !bare
    | Core.Type.Global_app {type_arguments = args; _} -> List.iter scan args
    | Core.Type.Arrow {parameter = a; result = b} ->
      scan a;
      scan b
    | Core.Type.Meta {contents = Some t} -> scan t
    | _ -> ()
  in
  List.iter scan doms;
  let in_doms =
    Hashtbl.fold (fun i () acc -> IntSet.add i acc) applied IntSet.empty
  in
  let in_doms = IntSet.diff in_doms !bare in
  bare := IntSet.empty;
  Hashtbl.reset applied;
  scan ret;
  let in_ret =
    IntSet.union
      !bare
      (Hashtbl.fold (fun i () acc -> IntSet.add i acc) applied IntSet.empty)
  in
  IntSet.diff in_doms in_ret

(** The type variables [tys] uses as the event family of a reified tree.

    A reified monad's own spelling drops the family -- [itree E R] is
    [std::shared_ptr<ITree<R>>] -- and the families themselves are emitted as
    plain structs, because a [Type -> Type] inductive whose constructors sit at
    differing indices has no C++ template to be.  So there is never a template
    name to pass for such a variable, and declaring it
    [template <typename> class] leaves a parameter nothing can satisfy.

    The occurrence in the tree is what identifies the family; the application
    that would otherwise demand the higher kind is elsewhere in the signature
    ([trigger_cast' (e : E void) : itree E A] applies it in the domain and
    names it in the codomain).  That application is taken back off by
    {!Core_plan.Plan_templates.deapply_plain_tvars} once the kind is refused. *)
let event_family_core_tvars tys =
  let fams = ref IntSet.empty in
  (* A variable handed to a family position of a generated type -- the [E] of
     [itree E A] in vanilla extraction, where [itree] is no registered monad
     -- is a family too: the type's own header decided that position is one
     ([Table.is_family_ind_param]). *)
  let rec at_family_positions t =
    match resolve_meta t with
    | Core.Type.Global_app {head = r; type_arguments = args; _} ->
      List.iteri
        (fun i a ->
          ( if Table.is_family_ind_param r i then
              match resolve_meta a with
              | Core.Type.Variable {variable = v; _} | Core.Type.Variable_app {head = v; _} ->
                fams := IntSet.add v !fams
              | _ -> () );
          at_family_positions a )
        args
    | Core.Type.Variable_app {arguments = args; _} -> List.iter at_family_positions args
    | Core.Type.Arrow {parameter = a; result = b} -> at_family_positions a; at_family_positions b
    | _ -> ()
  in
  List.iter at_family_positions tys;
  (* Every variable standing in a family position is a family, however the
     families there are combined: in [itree (D +' E) R] both [D] and [E] are,
     and so is anything a sum nested inside it names. *)
  let rec families a =
    match resolve_meta a with
    | Core.Type.Variable {variable = v; _} | Core.Type.Variable_app {head = v; _} -> fams := IntSet.add v !fams
    | Core.Type.Global_app {type_arguments = args; _} -> List.iter families args
    | _ -> ()
  in
  let rec scan t =
    match t with
    | Core.Type.Global_app {head = r; type_arguments = (_ :: _ as args); _}
      when Table.is_monad r && Table.is_monad_reified r ->
      (* A reified monad parameterises on its result last; everything before
         it is the event family. *)
      List.iteri
        (fun i a -> if i < List.length args - 1 then families a)
        args;
      List.iter scan args
    | Core.Type.Global_app {type_arguments = args; _} | Core.Type.Variable_app {arguments = args; _} ->
      List.iter scan args
    | Core.Type.Arrow {parameter = a; result = b} -> scan a; scan b
    | Core.Type.Meta {contents = Some t} -> scan t
    | _ -> ()
  in
  List.iter scan tys;
  !fams

(** The type variables a Core signature genuinely demands be declared
    [template <typename> class] rather than plain [typename].

    Core never names a higher-kinded variable bare: [sum1 E F X] arrives as
    [sum1 (E ?) (F ?) X], every occurrence already applied.  So "is it applied"
    cannot be the question, and two things answer it instead.

    - It is applied to an argument that survived erasure.  [hk_map : (A -> B)
      -> M A -> M B] applies [M] at two different real types, and no single
      plain [typename] stands for both.
    - It is an argument of a {b generated} type constructor at a position
      that constructor's own header declares [template <typename> class]
      ({!Core_plan.Plan_templates.hkt_templates} records which), so whatever is written there
      has to be a template name.

    Neither holds for an event family threaded through custom mappings.
    [sum1 => "Sum1"] and [itree => "std::shared_ptr<ITree<%t1>>"] spell their
    own parameters, and they take a family at plain [typename] because the
    index it is applied at is erased -- what reaches C++ is the event struct
    itself.  Reading those occurrences as a demand for a higher kind is what
    made [E_trigger] take a template template argument no call site could
    supply.

    This is read off the Core type on purpose.  The converted C++ type at the
    point the kinds are chosen has not been through the signature relaxations,
    so the occurrences that would justify the higher kind are not yet in it;
    and a kind chosen from the C++ type cannot be demoted afterwards, because
    the declaration and every call that supplies the parameter must already
    agree on it. *)

let higher_kinded_core_tvars tys =
  let hk = ref IntSet.empty in
  let families = event_family_core_tvars tys in
  let demand i = if not (IntSet.mem i families) then hk := IntSet.add i !hk in
  (* A variable that occurs only as the argument of an applied variable is an
     index -- the [T] of [E ~> F], in [E T -> F T] -- and an application at an
     index is a family's, whose struct already has it erased.  One that also
     occurs on its own -- the [A] of [fmap : (A -> B) -> F A -> F B] -- is a
     real type, and applying at it asks for a template name. *)
  let index_vars =
    let as_arg = ref IntSet.empty and elsewhere = ref IntSet.empty in
    let rec scan ~under_app t =
      match resolve_meta t with
      | Core.Type.Variable {variable = j; _} ->
        if under_app then as_arg := IntSet.add j !as_arg
        else elsewhere := IntSet.add j !elsewhere
      | Core.Type.Variable_app {arguments = args; _} -> List.iter (scan ~under_app:true) args
      | Core.Type.Global_app {type_arguments = args; _} -> List.iter (scan ~under_app:false) args
      | Core.Type.Arrow {parameter = a; result = b} -> scan ~under_app:false a; scan ~under_app:false b
      | _ -> ()
    in
    List.iter (scan ~under_app:false) tys;
    IntSet.diff !as_arg !elsewhere
  in
  let survived_erasure a =
    match resolve_meta a with
    | Core.Type.Unknown | Core.Type.Erased _ | Core.Type.Meta _ | Core.Type.Open _ -> false
    | Core.Type.Variable {variable = j; _} -> not (IntSet.mem j index_vars)
    | _ -> true
  in
  let rec scan ~generated_arg t =
    match t with
    | Core.Type.Variable_app {head = i; arguments = args} ->
      (* Applied at something erasure did not take away, or written where a
         generated constructor expects a template name. *)
      if generated_arg || List.exists survived_erasure args
      then demand i;
      List.iter (scan ~generated_arg:false) args
    | Core.Type.Global_app {head = r; type_arguments = args; _} ->
      (* Only a position the constructor's header actually declares a
         template: [Core_plan.Plan_templates.hkt_templates] recorded which, and a family
         parameter it left plain takes the family's own struct. *)
      List.iteri
        (fun i a ->
          scan
            ~generated_arg:
              ((not (Table.is_custom r)) && Table.is_hkt_ind_param r i)
            a )
        args
    | Core.Type.Arrow {parameter = a; result = b} ->
      scan ~generated_arg:false a;
      scan ~generated_arg:false b
    | Core.Type.Meta {contents = Some t} -> scan ~generated_arg t
    | _ -> ()
  in
  List.iter (scan ~generated_arg:false) tys;
  !hk

let relaxed_higher_kinded_tvars core_ty =
  IntSet.inter (relaxed_applied_core_tvars core_ty) (higher_kinded_core_tvars [core_ty])

(** [hkt_arg_core_tvar_arities tys] maps a type variable to the arity it is
    higher-kinded at because [tys] hands it, bare, to a position another
    constructor declares [template <typename> class].

    Being applied is the usual evidence for the higher kind, and
    {!higher_kinded_core_tvars} and [Core_plan.Plan_templates.applied_tvar_arities] both look
    for it.  It is not the only evidence.  [raiseUB (E : Type -> Type)
    (S : Sub UBE E) (B : Type)] applies [E] nowhere -- its result is [list B],
    and in the Vellvm original the result [itree E X] loses the event
    parameter on the way to [ITree<X>] -- so [E] survives only as an argument
    of [Sub].  But [Sub] is itself emitted higher-kinded, so the declaration
    that omits the kind cannot type-check against its own parameter's type:
    [Sub<UBE, T1>] wants a template where [T1] is a [typename].

    The position's kind is not guessed here.  It was decided and recorded by
    {!Core_plan.Plan_templates.hkt_templates} when the constructor's own header was emitted,
    which is the same authority a {e use} of that constructor already consults
    to decide it must pass a bare template name. *)
let hkt_arg_core_tvar_arities tys =
  let arities = Hashtbl.create 4 in
  let rec scan t =
    match t with
    | Core.Type.Global_app {head = r; type_arguments = args; _} ->
      List.iteri
        (fun i a ->
          match (resolve_meta a, Table.hkt_ind_param_arity r i) with
          | Core.Type.Variable {variable = v; _}, Some arity -> Hashtbl.replace arities v arity
          | Core.Type.Variable_app {head = v; arguments = args}, Some _ ->
            Hashtbl.replace arities v (List.length args)
          | _ -> () )
        args;
      List.iter scan args
    | Core.Type.Variable_app {arguments = args; _} -> List.iter scan args
    | Core.Type.Arrow {parameter = a; result = b} -> scan a; scan b
    | Core.Type.Meta {contents = Some t} -> scan t
    | _ -> ()
  in
  List.iter scan tys;
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) arities []

(** Whether a function type returns a type variable that its arguments carry
    only as the type index of an inductive with several constructors.

    [eval : expr A -> A] is the shape.  Nothing in the argument's C++ type
    mentions [A] -- an index is stripped from the generated type -- so a call
    cannot deduce it; and because sibling constructors of [expr] fix different
    indices, the branches genuinely return different types.  No single template
    parameter stands for all of them, so the honest result type is [std::any],
    recovered at the call.

    Neither weaker shape qualifies.  A single-constructor inductive
    ([wrap A -> A]) fixes one index, so the function has one result type and a
    template parameter says it exactly.  And a variable the arguments also
    carry outside an index position is deducible as usual.  The variable is
    [Some n] for [Core.Type.Variable n], [None] where the result is no such variable. *)
let index_only_result_tvar core_ty =
  let rec split acc = function
    | Core.Type.Arrow {parameter = t1; result = t2} -> split (t1 :: acc) t2
    | Core.Type.Meta {contents = Some t} -> split acc t
    | res -> (acc, res)
  in
  let doms, res = split [] core_ty in
  match res with
  | (Core.Type.Variable {variable = n; _}) when doms <> [] ->
    (* [as_index]: variables an argument carries only as an index of a
       many-constructor inductive.  [elsewhere]: everything it carries in any
       other position, which is deducible and so disqualifies. *)
    let as_index = ref IntSet.empty and elsewhere = ref IntSet.empty in
    let rec tvars_of into = function
      | Core.Type.Variable {variable = i; _} -> into := IntSet.add i !into
      | Core.Type.Arrow {parameter = t1; result = t2} -> tvars_of into t1; tvars_of into t2
      | Core.Type.Global_app {type_arguments = ts; _} -> List.iter (tvars_of into) ts
      | Core.Type.Meta {contents = Some t} -> tvars_of into t
      | _ -> ()
    in
    let rec walk = function
      | Core.Type.Arrow {parameter = t1; result = t2} -> walk t1; walk t2
      | Core.Type.Global_app {head = GlobRef.IndRef (kn, i); type_arguments = ts; _} ->
        let nparams =
          match Table.get_ind_num_param_vars_opt kn with Some k -> k | None -> 0
        in
        let many_ctors =
          match Table.get_ind_nb_ctors_opt kn i with Some c -> c > 1 | None -> false
        in
        List.iteri
          (fun j t ->
            if j >= nparams && many_ctors then tvars_of as_index t else walk t )
          ts
      | Core.Type.Global_app {type_arguments = ts; _} -> List.iter walk ts
      | Core.Type.Meta {contents = Some t} -> walk t
      | t -> tvars_of elsewhere t
    in
    List.iter walk doms;
    if IntSet.mem n !as_index && not (IntSet.mem n !elsewhere) then Some n else None
  | _ -> None

let result_is_index_only_tvar core_ty = Option.has_some (index_only_result_tvar core_ty)

(** [explicit_tvar_prefix ~force_required cty] is how many of a signature's
    leading template parameters the signature does not represent, and which a
    call therefore has to spell out instead of leaving to deduction.

    Only a leading run counts.  C++ lets a call supply the first few template
    arguments and deduce the rest, but not skip one in the middle, so a
    phantom sitting behind a deducible parameter is out of reach this way and
    keeps its [void] default at the declaration.

    The declaration emitter ({!Core_plan.Plan_templates.phantom_aware_temps}) and the call
    emitter both read the count from here, off the callee's type alone, so
    they agree whichever is generated first.

    @param force_required  as in {!Core_plan.Plan_templates.phantom_aware_temps}: indices that
      count as represented even though they do not appear in [cty]. *)
let explicit_tvar_prefix ?(force_required = IntSet.empty) (cty : Cpp_ir.Lowered.Type.t) =
  match cty with
  | Function (dom, cod) ->
    let primary =
      IntSet.union (primary_tvar_indices dom cod) force_required
    in
    let indexed =
      List.sort
        (fun (x, _) (y, _) -> Int.compare x y)
        ( get_tvars_indexed cty
        @ IntSet.fold
            (fun i acc ->
              if List.exists (fun (j, _) -> j = i) (get_tvars_indexed cty) then
                acc
              else (i, tvar_id i) :: acc )
            force_required [] )
    in
    let rec count = function
      | (i, _) :: rest when not (IntSet.mem i primary) -> 1 + count rest
      | _ -> 0
    in
    count indexed
  | _ -> 0
