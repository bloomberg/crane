(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Pure ml_type / cpp_type predicates and transforms shared across
    translation.ml. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
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

(** Like {!ctor_struct_name_of_ref} but returns an [Id.t]. *)
let ctor_struct_id_of_ref ?(fallback_idx = 0) (c : GlobRef.t) : Id.t =
  Id.of_string (ctor_struct_name_of_ref ~fallback_idx c)

(** Resolve a chain of [Tmeta] indirections to the underlying type. *)
let rec resolve_tmeta = function
  | Miniml.Tmeta {contents = Some t} -> resolve_tmeta t
  | t -> t

(** Unify a template [cpp_type] with a concrete [cpp_type] to extract type
    variable bindings. Recursively walks matching type constructors ([Tglob],
    [Tfun], [Tref], [Tmod], [Tnamespace]) and collects [(id, concrete_ty)]
    pairs wherever [tmpl] has a [Tvar].

    @param tmpl  the template type (may contain [Tvar] holes)
    @param conc  the concrete type to unify against
    @return association list of type variable bindings *)
let rec extract_tvar_map tmpl conc =
  match (tmpl, conc) with
  | Tvar (_, Some id), _ -> [(id, conc)]
  | Tglob (g1, tys1, _), Tglob (g2, tys2, _)
    when globref_equal g1 g2
         && List.length tys1 = List.length tys2 ->
    List.concat (List.map2 extract_tvar_map tys1 tys2)
  | Tfun (args1, ret1), Tfun (args2, ret2)
    when List.length args1 = List.length args2 ->
    List.concat (List.map2 extract_tvar_map args1 args2)
    @ extract_tvar_map ret1 ret2
  | Tref t1, Tref t2 -> extract_tvar_map t1 t2
  | Tmod (_, t1), Tmod (_, t2) -> extract_tvar_map t1 t2
  | Tnamespace (_, t1), Tnamespace (_, t2) -> extract_tvar_map t1 t2
  | _ -> []

(** Search an ML type for the first self-referential or mutually-recursive
    subtype, returning its type arguments. Recurses into [Tglob] type
    arguments and resolves [Tmeta] indirections.

    @param is_self_or_mutual  predicate identifying self/mutual references
    @return [Some args] for the first matching [Tglob], or [None] *)
let rec find_self_ref_args ~is_self_or_mutual = function
  | Miniml.Tglob (r, args, _) when is_self_or_mutual r -> Some args
  | Miniml.Tglob (_, args, _) ->
    List.find_map (find_self_ref_args ~is_self_or_mutual) args
  | Miniml.Tmeta {contents = Some t} -> find_self_ref_args ~is_self_or_mutual t
  | _ -> None

(** Check if an ML type is directly erased (non-recursive, top-level only).
    Matches unresolved [Tmeta], [Tdummy], and [Tvar]. *)
let is_erased_ml_type = function
  | Miniml.Tmeta {contents = None} | Miniml.Tdummy _ | Miniml.Tvar _ -> true
  | _ -> false

(** Recursive check for erased sub-types inside an ML type.  Resolves [Tmeta]
    chains before checking, then recurses into [Tglob] type arguments. *)
let rec ml_type_contains_erased ty =
  match resolve_tmeta ty with
  | Miniml.Tmeta _ | Miniml.Tdummy _ | Miniml.Tvar _ -> true
  | Miniml.Tglob (_, tys, _) -> List.exists ml_type_contains_erased tys
  | _ -> false

(** Return the codomain of an ML type, chasing through arrows and meta
    indirections. For [A -> B -> C] this returns [C]. *)
let rec ml_codomain = function
  | Miniml.Tarr (_, t2) -> ml_codomain t2
  | Miniml.Tmeta {contents = Some t} -> ml_codomain t
  | t -> t

(** Count the number of non-erased (non-[Tdummy]) arrow levels in an ML type.
    For example [Tdummy -> A -> B -> C] counts as 2 (the dummy is skipped). *)
let rec count_ml_value_arrows = function
  | Miniml.Tarr (t1, t2) when not (Mlutil.isTdummy t1) ->
    1 + count_ml_value_arrows t2
  | Miniml.Tarr (_, t2) -> count_ml_value_arrows t2
  | Miniml.Tmeta {contents = Some t} -> count_ml_value_arrows t
  | _ -> 0

(** Check if the codomain of an ML type (after all arrows) is a type variable.
    When true, the type variable might hide additional arrows, so the arrow
    count is not reliable for over-application detection. *)
let rec ml_codomain_is_tvar = function
  | Miniml.Tarr (_, t2) -> ml_codomain_is_tvar t2
  | Miniml.Tmeta {contents = Some t} -> ml_codomain_is_tvar t
  | Miniml.Tvar _ | Miniml.Tvar' _ | Miniml.Tunknown -> true
  | _ -> false

(** Count the total number of arrow levels in an ML type (including erased). *)
let rec count_ml_arrows = function
  | Miniml.Tarr (_, t2) -> 1 + count_ml_arrows t2
  | _ -> 0

(** Check if an ML type is a monadic type (outermost constructor is a registered
    monad). Monadic non-function definitions are generated as zero-arg thunks,
    so bare references to them must be wrapped in a function call. *)
let is_monadic_ml_type ty =
  match resolve_tmeta ty with
  | Miniml.Tglob (r, _, _) -> Table.is_monad r
  | _ -> false

(** Check if an ML type is void (unit type mapped to C++ void). *)
let ml_type_is_void (ty : ml_type) : bool =
  match resolve_tmeta ty with
  | Tglob (r, _, _) -> is_void r
  | _ -> false

(** Check if an ML type is Rocq's [unit] type. *)
let ml_type_is_unit (ty : ml_type) : bool =
  match resolve_tmeta ty with
  | Tglob (r, _, _) -> Table.is_unit_type r
  | _ -> false

(** Check if a C++ type is the Unit enum (from Rocq's [unit]).
    After [convert_ml_type_to_cpp_type], Rocq's [unit] becomes a [Tnamespace]
    wrapping a [Tglob] referencing the unit inductive, or a bare [Tglob] for
    local references.  This detects it for codomain void-ification. *)
let is_cpp_unit_type = function
  | Tglob (GlobRef.IndRef _ as r, _, _) -> Table.is_unit_type r
  | Tnamespace (r, _) -> Table.is_unit_type r
  | _ -> false

(** Recursively replace Rocq's unit enum type with [Tvoid] in a C++ type.
    Handles both direct [Unit -> void] (sequential mode) and nested
    [shared_ptr<ITree<Unit>> -> shared_ptr<ITree<void>>] (reified mode). *)
let rec voidify_unit_in_type = function
  | t when is_cpp_unit_type t -> Tvoid
  | Tglob (r, args, ns) ->
    Tglob (r, List.map voidify_unit_in_type args, ns)
  | Tnamespace (r, t) ->
    Tnamespace (r, voidify_unit_in_type t)
  | Tshared_ptr t -> Tshared_ptr (voidify_unit_in_type t)
  | t -> t

(** Check if an ML type represents a void or unit type. *)
let ml_type_is_unit_or_void ty = ml_type_is_void ty || ml_type_is_unit ty

(** Filter out erased ([Tdummy]) types from a type list. *)
let filter_value_types = List.filter (fun t -> not (isTdummy t))

(** Test whether the codomain of an ML function type, after skipping [n]
    value-domain arrows, erases to [std::any] in the generated C++.

    A [Tvar], [Tvar'], or [Tunknown] codomain erases to [std::any] only when
    at least one [Tdummy Ktype] was encountered while traversing the domain.
    That marker identifies a higher-rank, universally-quantified function (e.g.
    [forall A : Type, A -> A]) whose C++ encoding stores arguments and results
    as [std::any].  A plain [Tvar i] with no preceding [Tdummy] is a named C++
    template parameter (e.g. [T2] in [T1 -> T2]) and must {b not} be treated
    as erased.

    [n] counts the value-domain arrows to skip before inspecting the codomain;
    pass [0] to query the type's immediate codomain.  The [?has_dummy] flag
    accumulates whether a [Tdummy Ktype] was seen; callers should omit it
    (defaults to [false]).  Note: [Tdummy Kprop] (erased proof) is skipped
    without setting [has_dummy] — a proof argument does not make the codomain
    [std::any]. *)
let rec ml_codomain_erases_to_any ?(has_dummy = false) n = function
  | Miniml.Tarr (t, rest) ->
    ( match t with
    | Miniml.Tdummy Miniml.Ktype ->
      ml_codomain_erases_to_any ~has_dummy:true n rest
    | _ when isTdummy t ->
      (* Tdummy Kprop / Kimplicit: erased proof/implicit, skip without
         setting has_dummy and without consuming a value-arg slot. *)
      ml_codomain_erases_to_any ~has_dummy n rest
    | _ ->
      if n > 0 then ml_codomain_erases_to_any ~has_dummy (n - 1) rest
      else false )
  | Miniml.Tvar _ | Miniml.Tvar' _ | Miniml.Tunknown -> n = 0 && has_dummy
  | Miniml.Tmeta {contents = Some t} -> ml_codomain_erases_to_any ~has_dummy n t
  | _ -> false

(** Return [true] if the C++ type contains any unresolved type variable
    ([Tvar] or [Tauto]).  Used by {!gen_type_conversion_expr} to decide whether
    a field needs a converting constructor call. *)
let rec contains_tvar = function
  | Tvar _ | Tauto -> true
  | Tglob (_, ts, _) | Tid (_, ts) | Tid_external (_, ts) ->
    List.exists contains_tvar ts
  | Tshared_ptr t | Tref t | Tptr t
  | Tmod (_, t) | Tnamespace (_, t) ->
    contains_tvar t
  | Tfun (args, ret) ->
    List.exists contains_tvar args || contains_tvar ret
  | Tvariant ts -> List.exists contains_tvar ts
  | _ -> false

let rec has_unbound_tvar bound_names = function
  | Tvar (_, Some name) -> not (List.exists (Id.equal name) bound_names)
  | Tvar (_, None) -> true
  | Tauto -> true
  | Tglob (_, ts, _) | Tid (_, ts) | Tid_external (_, ts) ->
    List.exists (has_unbound_tvar bound_names) ts
  | Tshared_ptr t | Tref t | Tptr t
  | Tmod (_, t) | Tnamespace (_, t) ->
    has_unbound_tvar bound_names t
  | Tfun (args, ret) ->
    List.exists (has_unbound_tvar bound_names) args || has_unbound_tvar bound_names ret
  | Tvariant ts -> List.exists (has_unbound_tvar bound_names) ts
  | _ -> false

(** Check if [g] is the Coq [option] inductive (rendered as
    [std::optional]).  Used to detect [optional<shared_ptr<T>>] patterns
    that need special inline cloning instead of copy construction. *)
let is_option_global g =
  let n = Common.pp_global_name Type g in
  String.equal n "option" || String.equal n "Option"

let is_prod_global g =
  let n = Common.pp_global_name Type g in
  String.equal n "prod" || String.equal n "Prod"

(** Structural equality on C++ types, ignoring [Tmod] const/static wrappers
    and [Tvar] name annotations.  Used to match the state parameter type
    against the state component of a [pair<S,R>] return type. *)
let rec cpp_ty_eq t1 t2 =
  let rec strip = function Tmod (_, t) | Tnamespace (_, t) -> strip t | t -> t in
  match (strip t1, strip t2) with
  | Tglob (g1, ts1, _), Tglob (g2, ts2, _) ->
    GlobRef.CanOrd.equal g1 g2
    && List.length ts1 = List.length ts2
    && List.for_all2 cpp_ty_eq ts1 ts2
  | Tvar (i1, _), Tvar (i2, _) -> i1 = i2
  | Tref t1', Tref t2' -> cpp_ty_eq t1' t2'
  | Tshared_ptr t1', Tshared_ptr t2' -> cpp_ty_eq t1' t2'
  | Tfun (d1, c1), Tfun (d2, c2) ->
    List.length d1 = List.length d2
    && List.for_all2 cpp_ty_eq d1 d2
    && cpp_ty_eq c1 c2
  | Tvoid, Tvoid -> true
  | Tauto, Tauto -> true
  | Tany, Tany -> true
  | _ -> false

let is_list_global g =
  let n = Common.pp_global_name Type g in
  String.equal n "list"

let list_ctor_struct_names (g : GlobRef.t) : string * string =
  match g with
  | GlobRef.IndRef (kn, i) ->
    let nil_ref = GlobRef.ConstructRef ((kn, i), 1) in
    let cons_ref = GlobRef.ConstructRef ((kn, i), 2) in
    ( ctor_struct_name_of_ref nil_ref,
      ctor_struct_name_of_ref cons_ref )
  | _ -> ("Nil", "Cons")

(** Check if a C++ type is a dummy type glob (e.g., dummy_type, dummy_prop,
    dummy_implicit). These arise from Tdummy Ktype/Kprop/Kimplicit in the ML
    AST, which convert_ml_type_to_cpp_type maps to Tglob(VarRef "dummy_type")
    etc. These intermediate markers are used by the filtering pipeline
    (gen_expr, eta_fun, gen_decl_for_pp) to detect erased parameters and drop
    them before they reach the C++ renderer — they should never appear in the
    final generated output. *)
let is_cpp_dummy_type = function
  | Minicpp.Tglob (GlobRef.VarRef id, [], _) ->
    let name = Id.to_string id in
    name = "dummy_type" || name = "dummy_prop" || name = "dummy_implicit"
  | _ -> false

(** [is_erased_type t] — true if [t] represents a type-erased position:
    either [Tany] ([std::any]) or a dummy glob (from proof/type erasure).
    At runtime these values are stored as [std::any] and need [any_cast]
    to recover the concrete type. *)
let is_erased_type t = t = Minicpp.Tany || is_cpp_dummy_type t

(** [is_all_erased t] — true iff [t] is directly erased OR all of its type
    arguments are recursively all-erased.  Ground types without arguments
    (e.g. [nat], [bool]) return false.  Examples:
    - [pair<any, any>] → true (both args erased)
    - [pair<any, pair<any, any>>] → true (nested, all leaves erased)
    - [pair<any, List<any>>] → true ([List<any>] has all-erased args)
    - [pair<uint64_t, any>] → false ([uint64_t] is concrete)
    Used to detect fully-erased tuple chains where the runtime encoding
    stores [pair<any,any>] at every level regardless of the static type. *)
let rec is_all_erased = function
  | ty when is_erased_type ty -> true
  | Tglob (_, args, _) when args <> [] -> List.for_all is_all_erased args
  | _ -> false

(** [extract_template_args ty] — unwrap namespace and shared_ptr wrappers
    to extract the template arguments from the innermost [Tglob].
    Returns [\[\]] if no [Tglob] is found.

    For example, [Tnamespace(ns, Tglob(g, \[T1; T2\], _))] returns [\[T1; T2\]]. *)
let rec extract_template_args = function
  | Tglob (_, args, _) -> args
  | Tnamespace (_, inner) -> extract_template_args inner
  | Tshared_ptr inner -> extract_template_args inner
  | _ -> []

(** [erase_type_to_any ty] — recursively replace leaf types with [Tany],
    preserving the structure of container types ([Tglob] with args) and
    namespace wrappers.  Used to build the cast type for [any_cast] on
    erased container fields—e.g. [deque<pair<nat, bool>>] becomes
    [deque<any>].

    Note: the variant in {!eta_fun} that preserves bare [Tglob(_,\[\],_)]
    has intentionally different semantics and remains local. *)
and erase_type_to_any = function
  | Tglob (g, args, ns) when args <> [] ->
    Tglob (g, List.map erase_type_to_any args, ns)
  | Tnamespace (ns_g, inner) ->
    Tnamespace (ns_g, erase_type_to_any inner)
  | _ -> Tany

(** [is_ml_erased_ty ty] — true if [ty] represents an erased position in the
    ML AST: a bare type variable, [Tunknown], or an empty [Tmeta].  These
    arise from type-level parameters that were erased during extraction
    and correspond to [std::any] in the C++ representation. *)
and is_ml_erased_ty = function
  | Miniml.Tvar _ | Miniml.Tvar' _ | Miniml.Tunknown -> true
  | Miniml.Tmeta {contents = None} -> true
  | Miniml.Tmeta {contents = Some t} -> is_ml_erased_ty t
  | _ -> false

(** Check if a C++ type is a skipped type (inline custom with empty string).
    Such types arise from [Crane Extract Skip] and represent infrastructure
    (e.g. ReSum) that should be completely erased. *)
let is_skipped_cpp_type = function
  | Minicpp.Tglob (r, _, _) ->
    Table.is_inline_custom r && Table.find_custom_opt r = Some ""
  | _ -> false

(** Check if an ML type is a skipped type (inline custom with empty string).
    Same semantics as [is_skipped_cpp_type] but operates on the ML AST.
    Used to filter out parameters whose type was [Crane Extract Skip]-ped
    (e.g. [ReSum]-typed typeclass parameters from the ITree library). *)
let is_skipped_ml_type = function
  | Miniml.Tglob (r, _, _) ->
    Table.is_inline_custom r && Table.find_custom_opt r = Some ""
  | _ -> false

(** Recursively check whether a C++ type contains Tany (std::any). Used to
    detect when a let-binding's type annotation has unresolved carrier
    projections that should be replaced by concrete types from the generated
    lambda expression. *)
let rec has_tany_in_type = function
  | Tany -> true
  | Tvar (_, None) -> true  (* unnamed Tvar erases to std::any via tvar_erase_type *)
  | Tfun (dom, cod) -> List.exists has_tany_in_type dom || has_tany_in_type cod
  | Tmod (_, t) | Tnamespace (_, t) -> has_tany_in_type t
  | Tshared_ptr t | Tref t | Tptr t -> has_tany_in_type t
  | Tglob (_, ts, _) | Tid (_, ts) | Tid_external (_, ts) ->
    List.exists has_tany_in_type ts
  | Tvariant ts -> List.exists has_tany_in_type ts
  | Tqualified (base, _) -> has_tany_in_type base
  | _ -> false

(** Like [has_tany_in_type] but also treats [dummy_type]/[dummy_prop]/[dummy_implicit]
    VarRef markers as erased types.  Used for non-lambda let bindings where [auto]
    is the right fallback — but NOT for the Tfun+lambda case where we want to
    preserve the lambda's concrete return type. *)
let rec has_erased_type_in_type = function
  | t when has_tany_in_type t -> true
  | Tglob (GlobRef.VarRef id, [], [])
    when Id.to_string id = "dummy_type" -> true
  | Tfun (dom, cod) -> List.exists has_erased_type_in_type dom || has_erased_type_in_type cod
  | Tmod (_, t) | Tnamespace (_, t) -> has_erased_type_in_type t
  | Tshared_ptr t | Tref t | Tptr t -> has_erased_type_in_type t
  | Tglob (_, ts, _) | Tid (_, ts) | Tid_external (_, ts) ->
    List.exists has_erased_type_in_type ts
  | Tvariant ts -> List.exists has_erased_type_in_type ts
  | Tqualified (base, _) -> has_erased_type_in_type base
  | _ -> false

(** Check if a C++ type is the [dummy_prop] marker from proof erasure.

    In the extraction pipeline, [Tdummy Kprop] in the ML AST gets converted
    to [Tglob(VarRef "dummy_prop", [], [])] in the C++ AST by
    [convert_ml_type_to_cpp_type]. This marker occupies Kill Kprop positions
    to maintain positional alignment during type argument processing, but it
    has no corresponding C++ template parameter.

    These markers must be stripped before the "all or nothing" erased type
    check in [filter_erased_type_args]. If we don't strip them first, their
    presence would trigger the erasure of all type arguments (since [dummy_prop]
    is technically an "erased" type), even when the other type arguments are
    concrete and should be preserved.

    Example:
    - ML type args: [[Tglob nat; Tdummy Kprop; Tglob bool]]
    - After conversion: [[Tglob nat; Tglob dummy_prop; Tglob bool]]
    - After stripping dummy_prop: [[Tglob nat; Tglob bool]]
    - After filtering: [[Tglob nat; Tglob bool]] (preserved)

    Without stripping dummy_prop first:
    - Would see [Tglob dummy_prop] as erased → drop all args → [[]]

    @param t C++ type to check
    @return [true] if [t] is the dummy_prop marker, [false] otherwise *)
let is_cpp_dummy_prop = function
  | Minicpp.Tglob (GlobRef.VarRef id, [], _) ->
    Id.to_string id = "dummy_prop"
  | _ -> false

(** Filter erased type arguments from a template argument list using a
    two-phase approach: proof erasure stripping followed by all-or-nothing
    type erasure.

    Phase 1: Strip proof-erasure markers ([dummy_prop] from [Tdummy Kprop]).
    These are positional placeholders in the ML AST that have no C++ analog.
    They must be removed before checking for erased types, otherwise their
    presence would trigger full erasure of concrete type arguments.

    Phase 2: Apply the "all or nothing" rule for erased types.
    If ANY remaining type argument is erased (marked as [Tany] or [dummy_type]
    / [dummy_implicit]), drop ALL type arguments and return [[]]  .

    The "all or nothing" rule is required because C++ template arguments are
    positional. If we kept some type args and dropped others, the remaining
    args would shift into the wrong parameter positions, causing type mismatches.

    Dropping all args is safe because C++ template argument deduction can
    infer type arguments from value arguments at the call site. For example:
    - [std::make_optional(5u)] deduces [std::optional<unsigned int>]
    - [std::vector v{1, 2, 3}] deduces [std::vector<int>]

    This function is called at multiple points in the translation pipeline:
    - [gen_expr] (MLglob case): filter type args before emitting C++ call
    - [gen_expr_custom_cons]: filter before applying custom syntax template
    - [eta_fun]: filter when generating eta-expanded function wrappers
    - [gen_decl_for_pp]: filter when generating type declarations

    Example scenarios:

    1. Concrete types (no erasure):
       Input: [[Tglob nat; Tglob bool]]
       Output: [[Tglob nat; Tglob bool]]

    2. Proof in middle (strip but keep others):
       Input: [[Tglob nat; Tglob dummy_prop; Tglob bool]]
       After phase 1: [[Tglob nat; Tglob bool]]
       Output: [[Tglob nat; Tglob bool]]

    3. Erased type in middle (drop all):
       Input: [[Tglob nat; Tglob dummy_type; Tglob bool]]
       After phase 1: [[Tglob nat; Tglob dummy_type; Tglob bool]]
       After phase 2: [[]] (erased)

    4. Only proofs (drop all):
       Input: [[Tglob dummy_prop; Tglob dummy_prop]]
       After phase 1: [[]]
       Output: [[]]

    @param tys List of C++ types (template arguments)
    @return Filtered list: either all concrete types or empty list *)
let filter_erased_type_args ?(preserve_positions = false) tys =
  let tys = List.filter (fun t -> not (is_cpp_dummy_prop t)) tys in
  if preserve_positions then
    List.map (fun t -> if is_erased_type t then Minicpp.Tany else t) tys
  else if List.exists is_erased_type tys then [] else tys

(** Recursively check whether a C++ type tree contains erased HKT markers (Tany
    or dummy_type globs). These markers arise when a higher-kinded type
    constructor (e.g., F : Type -> Type) is erased during extraction — the type
    constructor itself becomes Tany/dummy_type, but it may be nested inside a
    function type like (A -> B) -> F A -> F B. Used by gen_dfun and
    gen_decl_for_pp to detect function params whose type variables cannot be
    deduced by C++ and should therefore use plain TTtypename instead of a
    TTfun (is_invocable_v) constraint. *)
let rec has_hkt_erasure = function
  | Minicpp.Tany -> true
  | t when is_cpp_dummy_type t -> true
  | Minicpp.Tfun (d, c) -> List.exists has_hkt_erasure d || has_hkt_erasure c
  | Minicpp.Tmod (_, t)
   |Minicpp.Tref t
   |Minicpp.Tshared_ptr t
   |Minicpp.Tnamespace (_, t) -> has_hkt_erasure t
  | Minicpp.Tglob (_, ts, _) | Minicpp.Tvariant ts ->
    List.exists has_hkt_erasure ts
  | _ -> false

(** Check if an ML type contains any unresolved type variable or placeholder.
    Returns true for Tvar, Tvar', unresolved Tmeta, and Tunknown. Used to guard
    Tvar substitution: we only substitute with fully concrete types. *)
let rec has_tvar = function
  | Miniml.Tvar _ | Miniml.Tvar' _ -> true
  | Miniml.Tunknown -> true
  | Miniml.Tarr (t1, t2) -> has_tvar t1 || has_tvar t2
  | Miniml.Tglob (_, args, _) -> List.exists has_tvar args
  | Miniml.Tmeta {contents = Some t} -> has_tvar t
  | Miniml.Tmeta {contents = None} -> true
  | _ -> false

(** Apply a type-level transformation to every type annotation in an ML AST. *)
let rec map_types_in_ast (f : ml_type -> ml_type) = function
  | MLlam (id, ty, body) -> MLlam (id, f ty, map_types_in_ast f body)
  | MLletin (id, ty, a, b) ->
    MLletin (id, f ty, map_types_in_ast f a, map_types_in_ast f b)
  | MLglob (r, tys) -> MLglob (r, List.map f tys)
  | MLcons (ty, r, args) -> MLcons (f ty, r, List.map (map_types_in_ast f) args)
  | MLcase (ty, e, brs) ->
    MLcase
      ( f ty,
        map_types_in_ast f e,
        Array.map
          (fun (ids, ty, pat, body) ->
            ( List.map (fun (id, t) -> (id, f t)) ids,
              f ty,
              pat,
              map_types_in_ast f body ) )
          brs )
  | MLfix (i, ids, funs, cf) ->
    MLfix
      ( i,
        Array.map (fun (n, ty) -> (n, f ty)) ids,
        Array.map (map_types_in_ast f) funs,
        cf )
  | MLapp (fn, args) ->
    MLapp (map_types_in_ast f fn, List.map (map_types_in_ast f) args)
  | MLmagic a -> MLmagic (map_types_in_ast f a)
  | MLparray (arr, def) ->
    MLparray (Array.map (map_types_in_ast f) arr, map_types_in_ast f def)
  | MLtuple args -> MLtuple (List.map (map_types_in_ast f) args)
  | ( MLrel _
    | MLexn _
    | MLdummy _
    | MLaxiom _
    | MLuint _
    | MLfloat _
    | MLstring _ ) as t -> t

(** Apply a Tvar substitution to an ML type. *)
let rec subst_tvars_type subst = function
  | Miniml.Tvar i | Miniml.Tvar' i ->
    ( match List.assoc_opt i subst with
    | Some t -> t
    | None -> Miniml.Tvar i )
  | Miniml.Tarr (a, b) ->
    Miniml.Tarr (subst_tvars_type subst a, subst_tvars_type subst b)
  | Miniml.Tglob (r, args, a) ->
    Miniml.Tglob (r, List.map (subst_tvars_type subst) args, a)
  | Miniml.Tmeta {contents = Some t} -> subst_tvars_type subst t
  | t -> t

(** Replace all unnamed Tvars with Tany (for type erasure in indexed
    inductives). Used when a type has Tvars that don't correspond to any
    template parameters. This is defined early so it can be used in
    gen_match_branch and gen_ind_header_v2. *)
let rec tvar_erase_type (ty : cpp_type) : cpp_type =
  match ty with
  | Tvar (_, None) -> Tany
  | Tvar (_, Some _) -> ty (* Named Tvars are kept *)
  | Tglob (r, tys, args) -> Tglob (r, List.map tvar_erase_type tys, args)
  | Tfun (tys, ty) -> Tfun (List.map tvar_erase_type tys, tvar_erase_type ty)
  | Tmod (m, ty) -> Tmod (m, tvar_erase_type ty)
  | Tnamespace (r, ty) -> Tnamespace (r, tvar_erase_type ty)
  | Tref ty -> Tref (tvar_erase_type ty)
  | Tvariant tys -> Tvariant (List.map tvar_erase_type tys)
  | Tshared_ptr ty -> Tshared_ptr (tvar_erase_type ty)
  | Tid (id, tys) -> Tid (id, List.map tvar_erase_type tys)
  | Tid_external (id, tys) -> Tid_external (id, List.map tvar_erase_type tys)
  | Tqualified (ty, id) -> Tqualified (tvar_erase_type ty, id)
  | _ -> ty (* Tvoid, Ttodo, Tunknown, Tany *)

(** Check if a C++ type contains any unnamed Tvar (Tvar(_, None)). Used to
    detect types that can't be fully resolved in monomorphized contexts
    (tvars=[]), where nested Tvar(_, None) would print as invalid C++ like
    List<T1>. *)
let rec has_unnamed_tvar (ty : cpp_type) : bool =
  match ty with
  | Tvar (_, None) -> true
  | Tvar (_, Some _) -> false
  | Tglob (_, tys, _) -> List.exists has_unnamed_tvar tys
  | Tfun (tys, ty) -> List.exists has_unnamed_tvar tys || has_unnamed_tvar ty
  | Tmod (_, ty) -> has_unnamed_tvar ty
  | Tnamespace (_, ty) -> has_unnamed_tvar ty
  | Tref ty -> has_unnamed_tvar ty
  | Tvariant tys -> List.exists has_unnamed_tvar tys
  | Tshared_ptr ty -> has_unnamed_tvar ty
  | Tid (_, tys) | Tid_external (_, tys) -> List.exists has_unnamed_tvar tys
  | Tqualified (ty, _) -> has_unnamed_tvar ty
  | _ -> false

(** Check if a C++ type is Tany or contains an unnamed Tvar (which becomes
    Tany). This is used to identify methods that return std::any due to type
    erasure in indexed inductives.  Also recognizes [Tglob(ConstRef c)] for
    non-custom, non-promoted constants — these are dependent type families
    (e.g. [Hom : Obj -> Obj -> Type]) whose C++ representation is [std::any].
    The extraction inlines type aliases, so surviving ConstRef types in C++
    types are genuinely unresolvable dependent type families. *)
let rec type_is_erased (ty : cpp_type) : bool =
  match ty with
  | Tany -> true
  | Tvar (_, None) -> true (* Will become Tany after tvar_erase_type *)
  | Tvar (_, Some _) -> false (* Named Tvar - not erased *)
  | Tglob (_, _, _) -> false
  | Tfun (_, _) -> false (* Functions aren't erased *)
  | Tmod (_, inner) -> type_is_erased inner
  | Tnamespace (_, inner) -> type_is_erased inner
  | _ -> false

(** Extract return type from a function type, stripping all Tarr layers. *)
let rec ml_return_type = function
  | Tarr (_, rest) -> ml_return_type rest
  | t -> t

(** Extract argument types and return type from a function type. *)
let rec get_args_and_ret acc = function
  | Tarr (t, rest) -> get_args_and_ret (t :: acc) rest
  | ret_ty -> (List.rev acc, ret_ty)

(** Strip [n] non-dummy arrow levels from an ML type, resolving Tmeta
    indirections and automatically skipping erased (Tdummy) arrows.
    Returns the codomain after stripping, or [None] if the type has fewer
    than [n] non-dummy arrow levels. *)
let rec strip_tarr_n n ty =
  if n <= 0 then Some ty
  else match resolve_tmeta ty with
    | Tarr (t1, rest) when Mlutil.isTdummy t1 ->
      (* Skip erased type-param arrow without consuming a real argument *)
      strip_tarr_n n rest
    | Tarr (_, rest) -> strip_tarr_n (n - 1) rest
    | _ -> None

(** Strip one level of reference or const-qualification from a C++ type.
    Normalises lambda parameter types before building [Tfun] wrappers.
    Unlike [Loopify.strip_ref_and_const_type] this is intentionally
    non-recursive: a double-ref [Tref (Tref t)] stays as [Tref t]. *)
let strip_cpp_ref_const = function
  | Tref t | Tmod (TMconst, t) -> t
  | t -> t

(** Count non-erased arguments in an ML application.
    [MLdummy] nodes represent erased type/proof parameters that are not
    passed to C++ functions; this returns the count of the remaining actual
    value arguments. *)
let count_real_ml_args args =
  List.length (List.filter (fun a ->
    match a with MLdummy _ -> false | _ -> true) args)

(** Check if a C++ type is a non-trivial value type (inductive struct),
    meaning it should be passed by value when owned and by const ref when
    borrowed, rather than by const value like primitives. *)
let is_inductive_value_type = function
  | Tglob (g, _, _) | Tnamespace (g, _) -> (
    match g with
    | GlobRef.IndRef _ ->
      not (is_enum_inductive g)
      && not (Table.is_coinductive g)
      && not (Table.is_custom_scalar_ref g)
    | _ -> false )
  | _ -> false

let is_trivially_copyable_type = function
  | Tglob (g, _, _) | Tnamespace (g, _) ->
    is_enum_inductive g || Table.is_custom_scalar_ref g
  | _ -> false

(** Check if an ML type maps to a non-trivially-copyable C++ value type.
    These are custom-extracted inductives (e.g., prod → std::pair) that are
    NOT shared_ptr-wrapped but still benefit from move semantics.
    Excluded: list (Datatypes::List contains shared_ptr<List> in Cons.l —
    moving a list value invalidates shared_ptr aliases to inner nodes). *)
let is_nontrivial_value_ml_type ty =
  match resolve_tmeta ty with
  | Miniml.Tglob (r, _, _) ->
    Table.is_custom r
    && not (Table.is_custom_scalar_ref r)
    && not (Escape.is_shared_ptr_type ty)
    && not (is_list_global r && not (Table.is_custom r))
  | _ -> false

let is_prod_ml_type ty =
  match resolve_tmeta ty with
  | Miniml.Tglob (r, _, _) -> is_prod_global r
  | _ -> false

(** Does a C++ type mention [shared_ptr] anywhere in its structure?
    Used to decide whether a field-type / bare-type mismatch in pattern
    matching is real (pointer wrapping) vs. superficial (namespace). *)
let rec contains_shared_ptr = function
  | Tshared_ptr _ -> true
  | Tref t | Tmod (_, t) | Tptr t -> contains_shared_ptr t
  | Tid (_, args) | Tid_external (_, args) | Tglob (_, args, _) ->
    List.exists contains_shared_ptr args
  | Tnamespace (_, t) -> contains_shared_ptr t
  | Tfun (args, ret) ->
    List.exists contains_shared_ptr args
    || contains_shared_ptr ret
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
