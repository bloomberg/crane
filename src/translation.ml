(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** {2 Conversion functions from Miniml to Minicpp types} *)

(** MiniML to MiniCpp translation: converts ML-style AST to C++-oriented AST. *)

open Common
open Miniml
open Minicpp
open Names
open Mlutil
open Table
open Str
open Util

(** Placeholder exception for unimplemented features *)
exception TODO

(** Compute the factory method name for a constructor.

    Factory names are the lowercase of the constructor struct name (e.g.,
    [Cons] → ["cons"]).  If the lowercased name collides with a C++ keyword
    (reuses {!Cpp_state.keywords} via {!Common.get_keywords}) or with the
    enclosing type's own name (which C++ treats as a constructor declaration),
    the original PascalCase is kept with a trailing underscore (e.g.,
    [Char] → ["Char_"]).

    @param type_name the enclosing inductive type's C++ name, for same-name
                     collision detection (default [""])
    @return the factory method name as a string *)
let factory_name_of_ctor ?(type_name = "") ctor_struct_name =
  let lc = String.lowercase_ascii ctor_struct_name in
  let collides =
    Id.Set.mem (Id.of_string lc) (get_keywords ())
    || lc = String.lowercase_ascii type_name
  in
  if collides then ctor_struct_name ^ "_"
  else lc

(** {2 Named Constructor Fields}

    Constructor struct fields in C++ are named using Rocq binder names when
    available.  For example, [Node (left : tree) (v : A) (right : tree)]
    generates fields [d_left], [d_v], [d_right] instead of [d_a0], [d_a1],
    [d_a2].

    The pipeline:
    + Extraction ({!Extraction.extract_really_ind}) populates
      {!Miniml.ml_ind_packet.ip_consarg_names} from the kernel binder names.
    + {!compute_and_register_field_names} transforms each binder into a
      C++-safe identifier and registers the mapping in
      {!Common.ctor_field_names}.
    + Access sites ({!gen_match_branch}, record reuse, {!Loopify.patch_cell_field})
      call {!Common.lookup_ctor_field_name} to resolve field names. *)

(** Sanitize a Rocq binder name for use as a C++ struct field identifier.

    Performs the following transformations:
    - Lowercases the name (Rocq names are often CamelCase)
    - Strips trailing primes ([a'] → [a], [x''] → [x])
    - Replaces non-alphanumeric characters (except [_]) with underscores

    Returns [None] if the result is empty or starts with a digit, in which
    case the caller falls back to the generic positional name [d_aJ].

    @param name  The raw Rocq binder name (e.g. ["left"], ["a'"], ["1st"]) *)
let sanitize_binder_name name =
  let lc = String.lowercase_ascii name in
  let len = String.length lc in
  (* Strip trailing primes: [a'''] → [a] *)
  let rec strip_end i =
    if i <= 0 then 0
    else if lc.[i - 1] = '\'' then strip_end (i - 1)
    else i
  in
  let end_pos = strip_end len in
  if end_pos = 0 then None
  else
    let s = String.sub lc 0 end_pos in
    (* Replace non-C++ chars with underscores *)
    let buf = Buffer.create (String.length s) in
    String.iter
      (fun c ->
        if (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_' then
          Buffer.add_char buf c
        else
          Buffer.add_char buf '_' )
      s;
    let result = Buffer.contents buf in
    if String.length result = 0 || (result.[0] >= '0' && result.[0] <= '9') then
      None
    else
      Some result

(** Derive the C++ field name string for constructor argument [k] from the
    binder name list [consarg_names].

    Returns ["d_<sanitized_name>"] when a valid binder name exists and does
    not collide with a C++ keyword, or the generic positional name
    ["d_a<k>"] otherwise.  This helper is factored out of
    {!compute_field_name} so that the deduplication check can call it for
    both the current index and all prior indices. *)
let field_name_str_of_idx consarg_names k =
  match List.nth_opt consarg_names k with
  | Some (Some id) -> (
    match sanitize_binder_name (Id.to_string id) with
    | Some sanitized ->
      if Id.Set.mem (Id.of_string sanitized) (get_keywords ()) then
        field_param_name k
      else
        "d_" ^ sanitized
    | None -> field_param_name k )
  | _ -> field_param_name k

(** Compute the C++ field name for field [j] of constructor struct
    [ctor_struct_name], register it in {!Common.ctor_field_names}, and
    return the resulting identifier.

    Handles three cases:
    - Named binder that is C++-safe → [d_<lowercase_name>] (e.g. [d_left])
    - Anonymous binder or keyword collision → [d_a<j>] (e.g. [d_a0])
    - Duplicate name within the same constructor → appends [_<j>] suffix

    @param ctor_struct_name  PascalCase name of the constructor struct
    @param consarg_names     binder names from {!ml_ind_packet.ip_consarg_names}
    @param n_fields          total field count (unused but kept for symmetry)
    @param j                 0-based field index *)
let compute_field_name ctor_struct_name consarg_names _n_fields j =
  let base_str = field_name_str_of_idx consarg_names j in
  (* Deduplicate: if an earlier field already has the same name, append the
     index as a suffix to disambiguate (e.g. [d_x] and [d_x_3]). *)
  let has_dup =
    let rec check k =
      if k >= j then false
      else if String.equal (field_name_str_of_idx consarg_names k) base_str
      then true
      else check (k + 1)
    in
    check 0
  in
  let field_str =
    if has_dup then base_str ^ "_" ^ string_of_int j else base_str
  in
  let field_id = Id.of_string field_str in
  register_ctor_field_name ctor_struct_name j field_id;
  field_id

(** Compute and register field names for all [n_fields] fields of a
    constructor struct.  Returns the list of field identifiers in order.

    This is the single entry point called from {!gen_ind_header_v2},
    {!gen_ind_header}, and {!gen_ind_cpp} at definition sites. *)
let compute_and_register_field_names ctor_struct_name consarg_names n_fields =
  List.init n_fields (fun j ->
    compute_field_name ctor_struct_name consarg_names n_fields j)

(** Derive the PascalCase C++ constructor struct name from a [GlobRef.t].

    Constructor references (e.g. [ConstructRef ((kn,0), 1)] for [Cons])
    are rendered as capitalized versions of their Rocq name; other references
    fall back to [Ctor<i>].  This is used at both definition sites (struct
    generation) and access sites (pattern matching, record reuse) to
    obtain the key for {!Common.lookup_ctor_field_name}.

    @param i  fallback index when the reference is not a [ConstructRef] *)
let ctor_struct_name_of_ref ?(fallback_idx = 0) (c : GlobRef.t) : string =
  match c with
  | GlobRef.ConstructRef _ ->
    String.capitalize_ascii (Common.pp_global_name Type c)
  | _ -> ctor_fallback_name fallback_idx

(** Like {!ctor_struct_name_of_ref} but returns an [Id.t]. *)
let ctor_struct_id_of_ref ?(fallback_idx = 0) (c : GlobRef.t) : Id.t =
  Id.of_string (ctor_struct_name_of_ref ~fallback_idx c)

(** Safe version of [List.firstn] that returns [min(n, length lst)] elements
    instead of raising [Failure "firstn"] when [n > length lst].

    This is a critical safety wrapper for type argument extraction. When
    [make_tyargs] in extraction.ml produces a type argument list that's
    shorter than expected (e.g., due to Tdummy Ktype erasure or failed type
    extraction), attempting to take the first N elements with [List.firstn]
    would crash with [Failure "firstn"].

    The shorter-than-expected list can occur when:
    - Type constructors are erased in fallback logic (Tdummy Ktype)
    - Higher-kinded type parameters fail extraction
    - Universe polymorphism causes extraction failures

    By using [safe_firstn], we gracefully handle these cases by taking as
    many elements as are available, up to the requested count. This allows
    the translation to proceed with partial type information rather than
    crashing during extraction.

    Example:
    - [safe_firstn 3 [a; b]] returns [[a; b]] (not [Failure "firstn"])
    - [safe_firstn 2 [a; b; c; d]] returns [[a; b]]

    @param n   Number of elements to take from the list (must be >= 0)
    @param lst Input list
    @return Prefix of [lst] with length [min(n, length lst)] *)
let safe_firstn n lst =
  let rec aux n lst acc =
    match n, lst with
    | 0, _ | _, [] -> List.rev acc
    | n, hd::tl -> aux (n-1) tl (hd::acc)
  in
  aux n lst []

(** Mutable context tracking inductives defined in the current module scope.
    When set, references to these inductives won't be wrapped in Tnamespace, so
    they appear as sibling types rather than outer-namespace-qualified types. *)
let local_inductives : GlobRef.t list ref = ref []

(** Register an inductive as local to the current module scope. *)
let add_local_inductive (r : GlobRef.t) =
  local_inductives := r :: !local_inductives

(** Clear the local inductives list (called at module boundaries). *)
let clear_local_inductives () = local_inductives := []

(** Return the list of inductives local to the current module scope. *)
let get_local_inductives () = !local_inductives

(** Helper to create CPPglob with pre-computed custom_info *)
let mk_cppglob (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  let ci =
    {
      ci_inline = (if Table.to_inline r then Table.find_custom_opt r else None);
      ci_is_custom = Table.is_custom r;
    }
  in
  CPPglob (r, tys, Some ci)

(** Helper for local variables (VarRef) - no custom extraction applies *)
let mk_cppglob_local (r : GlobRef.t) (tys : cpp_type list) : cpp_expr =
  CPPglob (r, tys, None)

(** Safe wrappers for Table lookups that may fail *)
let find_type_opt (r : GlobRef.t) : ml_type option =
  try Some (Table.find_type r) with Not_found -> None

(* ========================================================================== *)
(** Translation context — consolidated mutable state for expression compilation.
    All fields except local_inductives (which has a different lifecycle and is
    exported to cpp.ml) are grouped here in a single mutable record. *)
(* ========================================================================== *)

type translation_ctx = {
  mutable current_type_vars : Id.t list;
  mutable current_param_types : (int * ml_type) list;
  mutable current_outer_function_name : string option;
  (* C++ return type of the enclosing function, set by gen_dfun. Used to recover
     erased template type args at call sites where C++ can't deduce them from
     lambda arguments. *)
  mutable current_cpp_return_type : cpp_type option;
  mutable env_types : (Id.t * ml_type) list;
  mutable pending_lifted_decls : cpp_decl list;
  mutable current_letin_depth : int;
  mutable move_owned_vars : Escape.IntSet.t;
  mutable move_dead_after : Escape.IntSet.t;
  mutable move_suppress_tail : bool;
  mutable move_n_params : int;
  mutable match_param_counter : int;
  (* PROMOTED TYPE VARIABLES: Fields that were "promoted" from record values
     to type parameters during concept generation (see table.ml for details).

     [promoted_var_map] maps promoted field names to their C++ qualified types:
       Example: "m_carrier" ↦ Tqualified(Tvar "_tcI0", "m_carrier")
                prints as: typename _tcI0::m_carrier

     Set by [gen_dfun] when generating template functions with typeclass params.
     Used by [convert_ml_type_to_cpp_type] to resolve [Tvar(1000, name)] markers. *)
  mutable promoted_var_map : (Id.t * cpp_type) list;
  (* Context flag: are we inside a constructor expression (module-level static
     initializer)? When true, promoted type vars that can't be resolved via
     [promoted_var_map] fall back to [Tany] (std::any) instead of keeping
     [Tvar(1000, name)] markers, because module-level aliases apply. *)
  mutable in_constructor_expr : bool;
  (* ITree extraction mode: controls whether itree types are erased (Sequential)
     or preserved as std::shared_ptr<ITree<R>> (Reified) for observation. *)
  mutable itree_mode : itree_extraction_mode;
  (* When true, eta_fun keeps CPPmove wrappers on captured args and uses [&]
     capture instead of [=]. Set by the MLletin handler when it detects the
     bound variable is used at most once and does not escape. *)
  mutable eta_keep_moves : bool;
  (* Counter for generating unique [_cs] / [_cs1] / [_cs2] cache variable
     names when [Scustom_case] scrutinee caching is needed.  Reset at
     function boundaries, same pattern as [match_param_counter]. *)
  mutable cs_counter : int;
  (* When generating a method body, holds the set of self-references
     (the inductive type(s) this method belongs to).  Merged into the
     [ns] argument of [convert_ml_type_to_cpp_type] so that self-refs
     inside container types (e.g. [List<tree>]) get [shared_ptr] wrapping,
     matching the struct definition.  Empty outside method bodies. *)
  mutable method_self_ns : Refset'.t;
}

(** Mode for ITree effect extraction: sequential erases the tree,
    reified preserves it as [shared_ptr<ITree<R>>]. *)
and itree_extraction_mode =
  | Sequential  (* Default: erase itree E R to R, bind becomes ; *)
  | Reified     (* Preserve structure: itree E R becomes shared_ptr<ITree<R>> *)

(** The global mutable translation context, reset between top-level declarations. *)
let tctx =
  {
    current_type_vars = [];
    current_param_types = [];
    current_outer_function_name = None;
    current_cpp_return_type = None;
    env_types = [];
    pending_lifted_decls = [];
    current_letin_depth = 0;
    move_owned_vars = Escape.IntSet.empty;
    move_dead_after = Escape.IntSet.empty;
    move_suppress_tail = false;
    move_n_params = 0;
    match_param_counter = 0;
    promoted_var_map = [];
    in_constructor_expr = false;
    itree_mode = Sequential;
    eta_keep_moves = false;
    cs_counter = 0;
    method_self_ns = Refset'.empty;
  }

(** {3 Accessor wrappers} --- thin layer over {!tctx} fields. *)

(** Set the template type variables for the function currently being translated. *)
let set_current_type_vars (tvars : Id.t list) = tctx.current_type_vars <- tvars

(** Return the template type variables of the current function. *)
let get_current_type_vars () = tctx.current_type_vars

(** Reset the current type variables to the empty list. *)
let clear_current_type_vars () = tctx.current_type_vars <- []

(** Store 1-indexed parameter types for the current function.
    Used to recover erased type info at call sites. *)
let set_current_param_types (params : (Id.t * ml_type) list) =
  tctx.current_param_types <- List.mapi (fun i (_, ty) -> (i + 1, ty)) params

(** Look up an ML parameter type by its 1-based index. *)
let get_param_type_by_index (idx : int) : ml_type option =
  List.assoc_opt idx tctx.current_param_types

(** Reset the current parameter types to the empty list. *)
let clear_current_param_types () = tctx.current_param_types <- []

(** Enqueue a declaration to be lifted to the enclosing scope. *)
let add_lifted_decl (d : cpp_decl) =
  tctx.pending_lifted_decls <- d :: tctx.pending_lifted_decls

(** Drain and return the pending lifted declarations in definition order. *)
let take_lifted_decls () =
  let ds = List.rev tctx.pending_lifted_decls in
  tctx.pending_lifted_decls <- [];
  ds

(** Prepend bindings to the de Bruijn environment type stack. *)
let push_env_types (ids : (Id.t * ml_type) list) =
  tctx.env_types <- ids @ tctx.env_types

(** Retrieve the ML type of the variable at de Bruijn index [i] (1-based). *)
let get_env_type (i : int) : ml_type = snd (List.nth tctx.env_types (pred i))

(** Reset the environment type stack to empty. *)
let reset_env_types () = tctx.env_types <- []

(** Resolve a chain of [Tmeta] indirections to the underlying type. *)
let rec resolve_tmeta = function
  | Miniml.Tmeta {contents = Some t} -> resolve_tmeta t
  | t -> t

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

(** Extract the innermost result type from a (possibly monadic) ML type.
    For [nat -> itree ioE unit], returns [unit].
    For [nat -> unit], returns [unit].
    For [itree ioE unit] (zero-arg monadic), returns [unit].
    The result type is always the LAST type argument of the monad
    (monads parameterize on the result type as their last type param). *)
let ml_result_type ty =
  let cod = ml_codomain ty in
  match cod with
  | Miniml.Tglob (r, args, _) when Table.is_monad r ->
    (match List.rev args with r :: _ -> r | [] -> cod)
  | _ -> cod

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
  | Tunique_ptr t -> Tunique_ptr (voidify_unit_in_type t)
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
    accumulates whether a [Tdummy] was seen; callers should omit it (defaults
    to [false]). *)
let rec ml_codomain_erases_to_any ?(has_dummy = false) n = function
  | Miniml.Tarr (t, rest) ->
    if isTdummy t then ml_codomain_erases_to_any ~has_dummy:true n rest
    else if n > 0 then ml_codomain_erases_to_any ~has_dummy (n - 1) rest
    else false
  | Miniml.Tvar _ | Miniml.Tvar' _ | Miniml.Tunknown -> n = 0 && has_dummy
  | Miniml.Tmeta {contents = Some t} -> ml_codomain_erases_to_any ~has_dummy n t
  | _ -> false

(** Check if a monad reference uses the reified ITree extraction mode
    (i.e. its monad template string contains ["ITree"]). *)
let is_monad_reified monad_ref =
  match Table.get_monad_template_opt monad_ref with
  | Some t ->
    ( try ignore (Str.search_forward (Str.regexp_string "ITree") t 0); true
      with Not_found -> false )
  | None -> false

(** If the codomain of [ty] is a registered monad, return its reference. *)
let extract_monad_from_codomain ty =
  match ml_codomain ty with
  | Miniml.Tglob (monad_ref, _, _) when Table.is_monad monad_ref ->
    Some monad_ref
  | _ -> None

(** Collect [Id.t]s for typeclass-typed parameters in an ML arrow type. *)
let collect_typeclass_param_ids ty =
  let rec aux acc i = function
    | Miniml.Tarr (t1, t2) ->
      if Table.is_typeclass_type t1 then
        aux (tc_instance_id i :: acc) (i + 1) t2
      else
        aux acc i t2
    | _ -> List.rev acc
  in
  match ty with Miniml.Tarr _ -> aux [] 0 ty | _ -> []

(** Apply unit-to-void conversion on a C++ type, respecting reified mode.
    In reified mode, [Unit] inside [ITree<Unit>] becomes [ITree<void>].
    In sequential mode, the entire type becomes [Tvoid]. *)
let apply_unit_void unit_void is_reified ty =
  if unit_void then
    if is_reified then voidify_unit_in_type ty
    else Tvoid
  else ty

(** Generate the C++ expression for Rocq's [tt] (the unit constructor).
    Does NOT call [gen_expr] — it checks the extraction table directly. *)
let mk_tt_expr () =
  match Table.resolve_tt_ctor () with
  | Some tt_ref when Table.is_custom tt_ref ->
    mk_cppglob tt_ref []
  | Some tt_ref ->
    let ind_ref =
      match tt_ref with
      | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
      | _ ->
        CErrors.anomaly (Pp.str "mk_tt_expr: tt is not a ConstructRef")
    in
    let ctor_name =
      Id.of_string
        (Common.enum_ctor_name (Common.pp_global_name Type tt_ref))
    in
    CPPenum_val (ind_ref, ctor_name)
  | None ->
    CErrors.anomaly (Pp.str "mk_tt_expr: could not resolve core.unit.tt")

(** Check whether a global reference [r] has been void-ified: its ML type
    is a function (or monad) whose result type is [unit].  When such a
    function is called in expression context, the C++ call returns [void]
    and cannot be used as a value — we must wrap it in an IIFE that
    executes the call for side effects and returns [std::monostate{}]. *)
let is_void_ified_ref (r : GlobRef.t) : bool =
  match find_type_opt r with
  | Some ty ->
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty)
  | None -> false

(** Wrap a void-returning function call expression in an IIFE so it can
    be used in value context.  Produces:
      [&]() { void_call(); return std::monostate{}; }()
    The call is executed for side effects; the IIFE returns the unit value. *)
let wrap_void_call_as_value (call_expr : cpp_expr) : cpp_expr =
  CPPfun_call (
    CPPlambda ([], None,
      [Sexpr call_expr; Sreturn (Some (mk_tt_expr ()))],
      false),
    [])

(** Check whether an ML function expression [f] in [MLapp(f, args)] would
    produce a void-returning call in C++.  Handles:
    - [MLglob(r, _)]  — named function, look up type in extraction table
    - [MLrel(i)]       — variable (e.g. callback), look up type in env
    - [MLmagic(inner)] — transparent wrapper, recurse *)
let rec ml_callee_is_void = function
  | MLglob (r, _) -> is_void_ified_ref r
  | MLmagic inner -> ml_callee_is_void inner
  | MLrel i ->
    ( try
        let ty = get_env_type i in
        (match ty with Miniml.Tarr _ -> true
         | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
        && ml_type_is_unit (ml_result_type ty)
      with _ -> false )
  | _ -> false

(** {3 Reified ITree helpers}

    In reified mode, [itree E R] extracts to [std::shared_ptr<ITree<R>>]
    instead of being erased to [R].  The helpers below build C++ AST nodes
    for ITree types and constructors, and detect whether an ML expression
    already carries a reified tree value. *)

(** Extract the result type [R] from a monadic ML type [itree E R].
    Returns the second non-erased type argument, or [Miniml.Tunknown] if
    the type does not have the expected shape. *)
let extract_itree_result_ml (ml_ty : ml_type) : ml_type =
  match resolve_tmeta ml_ty with
  | Miniml.Tglob (_, _ :: r :: _, _) -> r
  | _ -> Miniml.Tunknown

(** Build the C++ type [std::shared_ptr<ITree<r_cpp>>]. *)
let mk_itree_type (r_cpp : cpp_type) : cpp_type =
  Tshared_ptr (Tid_external (Id.of_string "ITree", [r_cpp]))

(** True if [base] ends with ["Tree"] (possibly namespace-qualified). *)
let cpp_name_is_tree base =
  String.equal base "tree"
  || String.equal base "Tree"
  ||
  match String.rindex_opt base ':' with
  | Some i when i > 0 && i < String.length base - 1 && base.[i - 1] = ':' ->
    String.equal
      (String.sub base (i + 1) (String.length base - i - 1))
      "Tree"
  | _ -> false

(** Map well-known identifier names to their C++ equivalents.
    Returns [None] for ordinary (non-special) identifiers. *)
let resolve_special_id s =
  if String.equal s "int0" then Some "int64_t"
  else if String.equal s "string" then Some "std::string"
  else if String.equal s "dummy_type"
       || String.equal s "dummy_prop"
       || String.equal s "dummy_implicit"
  then Some "std::any"
  else None

(** Resolve a [VarRef] identifier to its C++ type name.
    Extends {!resolve_special_id} with additional known aliases
    like [prod] → [std::pair], [option] → [std::optional]. *)
let resolve_varref_id s =
  match resolve_special_id s with
  | Some r -> r
  | None ->
    if String.equal s "prod" || String.equal s "Prod" then "std::pair"
    else if String.equal s "option" || String.equal s "Option" then
      "std::optional"
    else if String.equal s "list" then "List"
    else s

(** Resolve an [IndRef] to its base C++ type name.  When the reference is
    in [raw_inductives], returns the raw Coq name; otherwise computes the
    C++ struct name with standard mappings (e.g. [prod] → [std::pair]).
    [~with_option] controls whether [option] maps to [std::optional] (only
    meaningful for zero-argument occurrences). *)
let resolve_indref_base ?(no_custom_inductives = Refset'.empty)
    ~raw_inductives ~with_option r =
  if Refset'.mem r raw_inductives then
    Common.pp_global_name Type r
  else
    let base = Common.pp_global_name Type r in
    let cap = Common.capitalize_last_component base in
    let parent_is_cap =
      match r with
      | GlobRef.IndRef (kn, _) ->
        ( match Names.MutInd.modpath kn with
        | Names.ModPath.MPdot (_, label) ->
          String.equal cap (Names.Label.to_string label)
        | _ -> false )
      | _ -> false
    in
    let skip_custom = Refset'.mem r no_custom_inductives in
    if (not skip_custom) && String.equal base "prod" then "std::pair"
    else if (not skip_custom) && with_option
         && (String.equal base "option" || String.equal base "Option")
    then "std::optional"
    else if parent_is_cap || String.equal base "nat" then cap
    else if
      List.exists
        (Environ.QGlobRef.equal Environ.empty_env r)
        (get_local_inductives ())
    then Common.pp_global Type r
    else cap

(** Render a C++ type as a plain string.  Used in [ITree<R>] qualified
    expressions, [clone_as_value<T>] template arguments, and anywhere a
    type must be serialised to a raw string.  Handles common built-in
    types; falls back to ["auto"] for unknown shapes. *)
let rec render_cpp_type_simple ?(raw_inductives = Refset'.empty)
    ?(no_custom_inductives = Refset'.empty) ty =
  let render = render_cpp_type_simple ~raw_inductives ~no_custom_inductives in
  let with_args base ts =
    match ts with [] -> base | _ ->
    base ^ "<" ^ String.concat ", " (List.map render ts) ^ ">"
  in
  match ty with
  | Tid (id, ts) ->
    let s = Id.to_string id in
    let base = match resolve_special_id s with Some r -> r | None -> s in
    with_args base ts
  | Tglob (r, ts, _) ->
    let base =
      match Table.find_custom_opt r with
      | Some s
        when (not (Refset'.mem r no_custom_inductives))
             && Table.to_inline r && not (String.contains s '%') ->
        s
      | _ ->
      match r with
      | GlobRef.IndRef _ ->
        resolve_indref_base ~no_custom_inductives ~raw_inductives
          ~with_option:true r
      | GlobRef.VarRef id -> resolve_varref_id (Id.to_string id)
      | _ -> Common.pp_global_name Type r
    in
    with_args base ts
  | Tid_external (id, ts) -> with_args (Id.to_string id) ts
  | Tnamespace (g, t) ->
    (* For local inductives whose names are eponymous with their parent module,
       no qualification is needed.  For others, prepend the capitalized parent
       module name (e.g., "NestedTree::tree").  We cannot use pp_global_name
       here because it gives the raw Coq name ("list" → "list") instead of
       the C++ struct name ("List"). *)
    if Table.is_enum_inductive g then
      let base = Common.pp_global_name Type g in
      let enum_name = Common.capitalize_last_component base in
      if
        List.exists
          (Environ.QGlobRef.equal Environ.empty_env g)
          (get_local_inductives ())
      then enum_name
      else (
        match g with
        | GlobRef.IndRef (kn, _) ->
          ( match Names.MutInd.modpath kn with
          | Names.ModPath.MPdot (_, label) ->
            Names.Label.to_string label ^ "::" ^ enum_name
          | _ -> enum_name )
        | _ -> enum_name )
    else if not (get_record_fields g == []) then render t
    else
    let inner = render t in
    let parent_ns =
      match g with
      | GlobRef.IndRef (kn, _) ->
        ( match Names.MutInd.modpath kn with
        | Names.ModPath.MPdot (_, label) ->
          let parent = Names.Label.to_string label in
          (* Strip template args before comparing: "List<t_A>" → "List" *)
          let inner_base =
            match String.index_opt inner '<' with
            | Some i -> String.sub inner 0 i
            | None -> inner
          in
          let cap_inner = Common.capitalize_last_component inner_base in
          (* Eponymous: parent "List" = inner "List" → no qualification *)
          if String.equal parent cap_inner then ""
          else parent ^ "::"
        | _ -> "" )
      | _ -> ""
    in
    parent_ns ^ inner
  | Tmod (TMconst, t) -> "const " ^ render t
  | Tmod (_, t) -> render t
  | Tref t -> render t ^ "&"
  | Tptr t -> render t ^ "*"
  | Tvar (_, Some n) ->
    let s = Id.to_string n in
    ( match resolve_special_id s with Some r -> r | None -> s )
  | Tshared_ptr t -> "std::shared_ptr<" ^ render t ^ ">"
  | Tunique_ptr t -> "std::unique_ptr<" ^ render t ^ ">"
  | Tvoid -> "void"
  | _ -> "auto"

(** Recursively wrap [Tglob] inductive references with [Tnamespace] so that
    [render_cpp_type_simple] produces fully-qualified names.  The [~skip]
    predicate controls which references are left unwrapped: [qualify_inductives]
    wraps all inductives, while [qualify_inductives ~skip:(Refset'.mem g set)]
    leaves members of [set] bare.  Used when the rendered type will appear in
    a context where inductives may not be in scope (e.g. [clone_as_value]
    template arguments in standalone free functions). *)
let rec qualify_inductives ?(skip = fun _ -> false) = function
  | Tglob (g, ts, es) ->
    let core = Tglob (g, List.map (qualify_inductives ~skip) ts, es) in
    ( match g with
    | GlobRef.IndRef _ when skip g -> core
    | GlobRef.IndRef _ -> Tnamespace (g, core)
    | _ -> core )
  | Tnamespace (g, t) -> Tnamespace (g, qualify_inductives ~skip t)
  | Tshared_ptr t -> Tshared_ptr (qualify_inductives ~skip t)
  | Tunique_ptr t -> Tunique_ptr (qualify_inductives ~skip t)
  | Tref t -> Tref (qualify_inductives ~skip t)
  | Tmod (m, t) -> Tmod (m, qualify_inductives ~skip t)
  | Tptr t -> Tptr (qualify_inductives ~skip t)
  | Tfun (args, ret) ->
    Tfun (List.map (qualify_inductives ~skip) args,
          qualify_inductives ~skip ret)
  | Tid (id, ts) -> Tid (id, List.map (qualify_inductives ~skip) ts)
  | Tid_external (id, ts) ->
    Tid_external (id, List.map (qualify_inductives ~skip) ts)
  | t -> t

(** Render a C++ type as a string suitable for use in raw C++ template
    arguments, applying post-hoc fixups for names that
    {!render_cpp_type_simple} emits in Coq form rather than C++ form
    (e.g. [int0] → [int64_t], [Uint64_t] → [Uint0]). *)
let render_cpp_type_for_raw_template ?(raw_inductives = Refset'.empty)
    ?(no_custom_inductives = Refset'.empty) ty =
  Str.global_replace
    (Str.regexp "\\<string\\>")
    "std::string"
    (Str.global_replace
       (Str.regexp_string "Uint64_t")
       "Uint0"
       (Str.global_replace
          (Str.regexp_string "int0")
          "int64_t"
          (render_cpp_type_simple ~raw_inductives ~no_custom_inductives ty)))

(** Return [true] if the C++ type contains any unresolved type variable
    ([Tvar] or [Tauto]).  Used by {!gen_clone_field_expr} to decide whether
    a field needs a converting constructor call. *)
let rec contains_tvar = function
  | Tvar _ | Tauto -> true
  | Tglob (_, ts, _) | Tid (_, ts) | Tid_external (_, ts) ->
    List.exists contains_tvar ts
  | Tshared_ptr t | Tunique_ptr t | Tref t | Tptr t
  | Tmod (_, t) | Tnamespace (_, t) ->
    contains_tvar t
  | Tfun (args, ret) ->
    List.exists contains_tvar args || contains_tvar ret
  | Tvariant ts -> List.exists contains_tvar ts
  | _ -> false

(** Return [true] if [g] is the Coq [option] inductive (rendered as
    [std::optional]).  Used to detect [optional<unique_ptr<T>>] patterns
    that need special inline cloning instead of copy construction. *)
let is_option_global g =
  let n = Common.pp_global_name Type g in
  String.equal n "option" || String.equal n "Option"

(** Render a simple C++ expression to a string for use in raw C++ fragments.
    Returns [None] for compound expressions that cannot be reduced to a
    simple identifier or dereference chain. *)
let rec render_cpp_expr_simple = function
  | CPPvar id -> Some (Id.to_string id)
  | CPPthis -> Some "this"
  | CPPderef e ->
    Option.map (fun s -> "(*" ^ s ^ ")") (render_cpp_expr_simple e)
  | CPPget (e, field) ->
    Option.map (fun s -> s ^ "." ^ Id.to_string field)
      (render_cpp_expr_simple e)
  | CPPget' (e, field_ref) ->
    Option.map (fun s -> s ^ "." ^ Common.pp_global_name Type field_ref)
      (render_cpp_expr_simple e)
  | CPPraw s -> Some s
  | _ -> None

(** Generate inline C++ clone code for a constructor field, converting
    from [src_ty] to [dst_ty].  For non-copyable types ([unique_ptr],
    [optional<unique_ptr>]) emits explicit inline clone code.  For
    everything else — including type variables — emits a plain copy,
    relying on the deep-copy copy constructor that every Crane-generated
    inductive type provides. *)
let gen_clone_field_expr ~src_ty ~dst_ty expr =
  let render ty = render_cpp_type_for_raw_template (qualify_inductives ty) in
  (* Strip a single [Tnamespace] wrapper when it matches the inner [Tglob].
     [convert_ml_type_to_cpp_type] wraps external inductives as
     [Tnamespace(g, Tglob(g,...))] for qualified rendering, but for pattern
     matching we want the bare [Tglob(g,...)] form. *)
  let strip_ns = function
    | Tnamespace (g, (Tglob (g2, _, _) as core)) when GlobRef.CanOrd.equal g g2 -> core
    | t -> t
  in
  let src_ty = strip_ns src_ty and dst_ty = strip_ns dst_ty in
  (* Inline clone for a [unique_ptr<T>] field: null-safe make_unique using
     the pointee's clone() method. *)
  let mk_uptr_clone inner_s expr_s =
    expr_s ^ " ? std::make_unique<" ^ inner_s ^ ">(" ^ expr_s
    ^ "->clone()) : nullptr"
  in
  (* Inline clone for [optional<unique_ptr<T>>] (same-type): null-check +
     make_optional + make_unique + ->clone(). *)
  let mk_opt_uptr_clone inner_s expr_s =
    expr_s ^ ".has_value() ? std::make_optional(std::make_unique<" ^ inner_s
    ^ ">((*" ^ expr_s ^ ")->clone())) : std::nullopt"
  in
  (* Convert [optional<unique_ptr<T>>] → [optional<T>]: null-check + clone
     the pointed-to value.  Uses clone() because T may have a deleted copy
     constructor (when T itself contains a [unique_ptr] field). *)
  let mk_opt_uptr_to_val dst_inner_s expr_s =
    expr_s ^ ".has_value() ? std::make_optional<" ^ dst_inner_s ^ ">((*"
    ^ expr_s ^ ")->clone()) : std::nullopt"
  in
  (* Helper: build a [CPPraw] using a string renderer, falling back to an
     IIFE lambda wrapper when [expr] cannot be rendered to a simple string.
     [lambda_ty] is the C++ return type for the wrapper. [make_body s] is
     called with either the rendered [expr] string or ["__x"] (the lambda
     param name). *)
  let with_expr_s ~lambda_ty ~make_body =
    match render_cpp_expr_simple expr with
    | Some s -> CPPraw (make_body s)
    | None ->
      let body = make_body "__x" in
      CPPfun_call
        ( CPPraw
            ("[](auto&& __x) -> " ^ lambda_ty ^ " { return " ^ body ^ "; }"),
          [expr] )
  in
  if src_ty = dst_ty then
    (* ---- Same type: deep-copy ---- *)
    match src_ty with
    | Tunique_ptr inner ->
      (* unique_ptr<T>: null-safe via ->clone() *)
      let inner_s = render inner in
      let ty_s = render src_ty in
      with_expr_s ~lambda_ty:ty_s ~make_body:(mk_uptr_clone inner_s)
    | Tglob (g, [Tunique_ptr inner], _) when is_option_global g ->
      (* optional<unique_ptr<T>>: null-safe element-wise clone *)
      let inner_s = render inner in
      let ty_s = render src_ty in
      with_expr_s ~lambda_ty:ty_s
        ~make_body:(mk_opt_uptr_clone inner_s)
    | Tglob (GlobRef.IndRef _ as g, _, _)
      when not (Table.is_inline_custom g) && not (Table.is_enum_inductive g) ->
      (* Crane-generated inductive struct (has clone()): call directly *)
      CPPfun_call (CPPmember (expr, Id.of_string "clone"), [])
    | _ ->
      (* Type variables, scalars, shared_ptr, type aliases, etc.: plain copy.
         Copy constructors deep-copy for Crane types; type variables are
         always bare types (never unique_ptr) because nested self-references
         are wrapped at the field level, not the type-argument level. *)
      expr
  else
    (* ---- Different types: dispatch on wrapper structure ---- *)
    match (src_ty, dst_ty) with
    | Tunique_ptr _src_inner, Tunique_ptr dst_inner ->
      (* unique_ptr<S> → unique_ptr<T>: null-check + dereference inner *)
      let dst_inner_s = render dst_inner in
      let ty_s = render dst_ty in
      with_expr_s ~lambda_ty:ty_s
        ~make_body:(fun s ->
          s ^ " ? std::make_unique<" ^ dst_inner_s ^ ">(*" ^ s ^ ") : nullptr")
    | Tunique_ptr inner, _ ->
      (* unique_ptr<T> → T: dereference; if inner type differs from dst,
         apply a converting constructor after dereferencing. *)
      let derefed = CPPderef expr in
      if inner = dst_ty then derefed
      else
        let dst_s = render dst_ty in
        CPPfun_call (CPPraw dst_s, [derefed])
    | Tshared_ptr inner, _ ->
      (* shared_ptr<T> → T: dereference; if inner type differs from dst,
         apply a converting constructor after dereferencing. *)
      let derefed = CPPderef expr in
      if inner = dst_ty then derefed
      else
        let dst_s = render dst_ty in
        CPPfun_call (CPPraw dst_s, [derefed])
    | _, Tunique_ptr inner ->
      (* T → unique_ptr<T>: wrap in make_unique *)
      CPPfun_call (CPPmk_unique inner, [expr])
    | Tglob (g1, [src_inner_ty], _), Tglob (g2, [dst_inner], _)
      when GlobRef.CanOrd.equal g1 g2 && is_option_global g1
           && (match src_inner_ty with
               | Tunique_ptr _ | Tshared_ptr _ -> true
               | _ -> false)
           && (match dst_inner with
               | Tunique_ptr _ | Tshared_ptr _ -> false
               | _ -> true) ->
      (* optional<unique_ptr<T>> or optional<shared_ptr<T>> → optional<T> *)
      let dst_inner_s = render dst_inner in
      let ty_s = render dst_ty in
      with_expr_s ~lambda_ty:ty_s
        ~make_body:(mk_opt_uptr_to_val dst_inner_s)
    | Tglob (g1, [src_inner], _), Tglob (g2, [Tunique_ptr dst_inner], _)
      when GlobRef.CanOrd.equal g1 g2 && is_option_global g1
           && (match src_inner with Tunique_ptr _ | Tshared_ptr _ -> false | _ -> true) ->
      (* optional<T> → optional<unique_ptr<T>> *)
      let dst_inner_s = render dst_inner in
      let ty_s = render dst_ty in
      with_expr_s ~lambda_ty:ty_s
        ~make_body:(fun s ->
          s ^ ".has_value() ? std::make_optional(std::make_unique<" ^ dst_inner_s
          ^ ">((*" ^ s ^ ").clone())) : std::nullopt")
    | Tglob (g1, [src_inner], _), Tglob (g2, [Tshared_ptr dst_inner], _)
      when GlobRef.CanOrd.equal g1 g2 && is_option_global g1
           && (match src_inner with Tunique_ptr _ | Tshared_ptr _ -> false | _ -> true) ->
      (* optional<T> → optional<shared_ptr<T>> *)
      let dst_inner_s = render dst_inner in
      let ty_s = render dst_ty in
      with_expr_s ~lambda_ty:ty_s
        ~make_body:(fun s ->
          s ^ ".has_value() ? std::make_optional(std::make_shared<" ^ dst_inner_s
          ^ ">((*" ^ s ^ ").clone())) : std::nullopt")
    | Tglob (g1, _src_ts, _), Tglob (g2, _dst_ts, _)
      when GlobRef.CanOrd.equal g1 g2 && _src_ts <> _dst_ts
           && not (Table.is_inline_custom g1) ->
      (* Same Crane container, different element types → converting ctor *)
      let dst_type_s = render dst_ty in
      CPPfun_call (CPPraw dst_type_s, [expr])
    | _ ->
      (* Type variables or fully concrete different types: converting
         constructor.  Type variables are always bare (never unique_ptr)
         because nested self-references are wrapped at the field level. *)
      let dst_s = render dst_ty in
      CPPfun_call (CPPraw dst_s, [expr])

(** Build a [CPPfun_call] for [ITree<R>::ret(...)].
    When [r_cpp] is [Tvoid], generates [ITree<void>::ret()]. *)
let mk_itree_ret (r_cpp : cpp_type) (args : cpp_expr list) : cpp_expr =
  let type_str =
    if r_cpp = Tvoid then "void" else render_cpp_type_simple r_cpp
  in
  CPPfun_call (
    CPPqualified (CPPraw ("ITree<" ^ type_str ^ ">"), Id.of_string "ret"),
    args)

(** Build [ITree<R>::ret(v)] or [ITree<void>::ret()] depending on whether
    the result type is void.  [r_cpp] is the C++ result type; [r_ml] is
    the ML result type (checked with {!ml_type_is_void} for unit-mapped
    types); [v] is the value expression to wrap. *)
let mk_itree_ret_for_value r_cpp r_ml v =
  if r_cpp = Tvoid || ml_type_is_unit_or_void r_ml then
    mk_itree_ret Tvoid []
  else
    mk_itree_ret r_cpp [v]

(** Reify a monadic parameter type for ITree extraction.

    In reified mode, the C++ type for a monadic parameter [itree E R] after
    monad erasure is just [R].  This function wraps it back into
    [shared_ptr<ITree<R>>] so the tree can be passed as a first-class value.
    Does nothing in sequential mode or when [ml_ty] is not monadic. *)
let reify_monadic_param_type ml_ty cpp_ty =
  if is_monadic_ml_type ml_ty && tctx.itree_mode = Reified then begin
    Table.require_itree_header ();
    let r_ty =
      match cpp_ty with
      | Tglob (_, _ :: r :: _, _) -> r
      | t -> t
    in
    (* Voidify unit result type inside ITree params *)
    let r_ty = if is_cpp_unit_type r_ty then Tvoid else r_ty in
    mk_itree_type r_ty
  end
  else cpp_ty

(** Check whether an ML expression is a de Bruijn reference to a variable
    whose [env_type] is monadic.  Such variables have been reified to
    [shared_ptr<ITree<R>>] and need [->run()] to extract the value. *)
let is_reified_monadic_var ml_expr =
  match ml_expr with
  | MLrel i ->
    (try is_monadic_ml_type (get_env_type i) with _ -> false)
  | _ -> false

(** Check whether an ML expression already produces a reified monadic value
    (a [shared_ptr<ITree<R>>]).  Extends {!is_reified_monadic_var} to also
    cover [MLapp(MLrel f, args)] where [f] is a local function whose return
    type is monadic.  Such calls already return a tree, so wrapping in
    [ITree::ret()] would incorrectly double-wrap.

    Does {b not} return [true] for [MLapp(MLglob g, args)] because global
    inline extractions (e.g. [print_endline]) may produce direct C++
    expressions that genuinely need Ret wrapping. *)
let is_reified_monadic_expr ml_expr =
  match ml_expr with
  | MLrel i ->
    (try is_monadic_ml_type (get_env_type i) with _ -> false)
  | MLapp (MLrel i, _) ->
    (try is_monadic_ml_type (ml_codomain (get_env_type i)) with _ -> false)
  | _ -> false

(** If [ml_expr] refers to a reified monadic variable, wrap [cpp_expr] in
    a [->run()] call to execute the tree and produce the direct value.
    Otherwise returns [cpp_expr] unchanged. *)
let deref_reified ml_expr cpp_expr =
  if is_reified_monadic_var ml_expr then
    CPPmethod_call (cpp_expr, Id.of_string "run", [])
  else
    cpp_expr

(** Convert returned lambdas to capture by value. Lambdas returned from
    functions outlive the function's stack frame, so capturing by reference
    ([&]) would create dangling references. This rewrites
    [Sreturn (Some (CPPlambda (_, _, _, false)))] to capture by value ([true]).
*)
let return_captures_by_value stmts =
  let rec expr = function
    | CPPlambda (args, ret, body, false) ->
      CPPlambda (args, ret, List.map stmt body, true)
    | CPPlambda (args, ret, body, true) ->
      CPPlambda (args, ret, List.map stmt body, true)
    | CPPfun_call (f, args) -> CPPfun_call (expr f, List.map expr args)
    | CPPderef e -> CPPderef (expr e)
    | CPPmove e -> CPPmove (expr e)
    | CPPforward (ty, e) -> CPPforward (ty, expr e)
    | CPPoverloaded es -> CPPoverloaded (List.map expr es)
    | CPPstruct (id, tys, es) -> CPPstruct (id, tys, List.map expr es)
    | CPPstruct_id (id, tys, es) -> CPPstruct_id (id, tys, List.map expr es)
    | CPPstructmk (id, tys, es) -> CPPstructmk (id, tys, List.map expr es)
    | CPPshared_ptr_ctor (ty, e) -> CPPshared_ptr_ctor (ty, expr e)
    | CPPunique_ptr_ctor (ty, e) -> CPPunique_ptr_ctor (ty, expr e)
    | CPPbinop (op, a, b) -> CPPbinop (op, expr a, expr b)
    | CPPunop (op, e) -> CPPunop (op, expr e)
    | CPPmember (e, id) -> CPPmember (expr e, id)
    | CPPqualified (e, id) -> CPPqualified (expr e, id)
    | CPPget (e, id) -> CPPget (expr e, id)
    | CPPget' (e, id) -> CPPget' (expr e, id)
    | CPPmethod_call (e, id, args) ->
      CPPmethod_call (expr e, id, List.map expr args)
    | CPPany_cast (ty, e) -> CPPany_cast (ty, expr e)
    | e -> e
  and stmt = function
    | Sreturn (Some e) -> Sreturn (Some (expr e))
    | Sexpr e -> Sexpr (expr e)
    | Sasgn (id, ty, e) -> Sasgn (id, ty, expr e)
    | Sderef_asgn (lhs, e) -> Sderef_asgn (expr lhs, expr e)
    | Sif (c, t, f) -> Sif (expr c, List.map stmt t, List.map stmt f)
    | Sswitch (scrut, ind, branches, default) ->
      Sswitch
        ( expr scrut,
          ind,
          List.map (fun (id, body) -> (id, List.map stmt body)) branches,
          Option.map (List.map stmt) default )
    | Smatch (branches, default) ->
      Smatch
        ( List.map
            (fun br ->
              { br with
                smb_scrutinee = expr br.smb_scrutinee;
                smb_body = List.map stmt br.smb_body })
            branches,
          Option.map (List.map stmt) default )
    | Scustom_case (ty, e, tys, branches, err) ->
      Scustom_case
        ( ty,
          expr e,
          tys,
          List.map
            (fun (ids, ctor, body) -> (ids, ctor, List.map stmt body))
            branches,
          err )
    | s -> s
  in
  List.map
    (fun s ->
      match s with
      | Sreturn (Some (CPPlambda (args, ret, body, false))) ->
        Sreturn (Some (CPPlambda (args, ret, body, true)))
      | Sreturn (Some e) -> Sreturn (Some (expr e))
      | s -> s )
    stmts

(** Run escape analysis on [body], saving and restoring the analysis state
    around the call to [f]. This is needed because escape analysis runs at
    multiple nesting levels (lambdas, let-in expressions, top-level functions)
    and each level has its own set of safe bindings. *)
let with_escape_analysis body f =
  let saved_depth = tctx.current_letin_depth in
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let saved_match_counter = tctx.match_param_counter in
  let saved_cs_counter = tctx.cs_counter in
  let saved_return_type = tctx.current_cpp_return_type in
  tctx.current_letin_depth <- 0;
  tctx.move_dead_after <- Escape.IntSet.empty;
  tctx.move_owned_vars <- Escape.IntSet.empty;
  tctx.move_n_params <- 0;
  tctx.match_param_counter <- 0;
  tctx.cs_counter <- 0;
  (* Prevent void optimization from leaking into IIFE/lambda bodies: when the
     outer function returns void, gen_stmts generates bare 'return;' for tt,
     but IIFE bodies return their own type (e.g. monostate), not void. *)
  ( if tctx.current_cpp_return_type = Some Tvoid then
      tctx.current_cpp_return_type <- None );
  let result = f () in
  tctx.current_letin_depth <- saved_depth;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  tctx.match_param_counter <- saved_match_counter;
  tctx.cs_counter <- saved_cs_counter;
  tctx.current_cpp_return_type <- saved_return_type;
  result

(** Save move-tracking state, shift de Bruijn indices by [n] binders, run [f],
    then restore the original state.  This is the standard bracket for code
    that introduces [n] pattern variables or let bindings.

    {b Why shift.}  [move_owned_vars] and [move_dead_after] track variables by
    de Bruijn index.  When entering a scope with [n] new binders, all existing
    indices must be shifted up by [n] so they continue to refer to the same
    outer variables.

    @param clear_dead  If [true], empty [move_dead_after] instead of shifting.
      Used inside match branches, which are independent scopes: the outer
      dead-after set must not leak in, because a variable dead after one branch
      may still be live in another.
    @param add_owned  Optional de Bruijn index to add to the owned set after
      shifting.  Used for monadic bind continuation parameters that receive an
      owned [shared_ptr] value (e.g. [>>=] callback arguments).
    @param exclude_owned  Optional de Bruijn index to REMOVE from the owned set
      after shifting.  Used for match scrutinees: after shifting by [n], the
      scrutinee's outer index [db] becomes [db + n].  Excluding it prevents
      [std::move(scrutinee)] from being emitted inside the branch while
      pattern-variable structured bindings ([const auto& [d_a0, d_a1] = ...])
      still hold const references into it — which would cause use-after-move. *)
let with_shifted_move_tracking n ?(clear_dead = false) ?add_owned ?exclude_owned f =
  let saved_owned = tctx.move_owned_vars in
  let saved_dead = tctx.move_dead_after in
  tctx.move_owned_vars <-
    Escape.IntSet.map (fun i -> i + n) tctx.move_owned_vars;
  ( match add_owned with
  | Some idx -> tctx.move_owned_vars <- Escape.IntSet.add idx tctx.move_owned_vars
  | None -> () );
  ( match exclude_owned with
  | Some idx -> tctx.move_owned_vars <- Escape.IntSet.remove idx tctx.move_owned_vars
  | None -> () );
  tctx.move_dead_after <-
    ( if clear_dead then Escape.IntSet.empty
      else Escape.IntSet.map (fun i -> i + n) tctx.move_dead_after );
  let result = f () in
  tctx.move_owned_vars <- saved_owned;
  tctx.move_dead_after <- saved_dead;
  result

(* ============================================================================
   Shared helpers for method generation (used by gen_ind_header_v2 and
   gen_record_methods)
   ============================================================================ *)

(** Re-export [IntSet] from [Escape] for local use in type variable collection. *)
module IntSet = Escape.IntSet

(** Collect all Tvar indices from an ml_type. Used to find type variables beyond
    those of the containing inductive/record. *)
let rec collect_tvars_set acc = function
  | Miniml.Tvar i | Miniml.Tvar' i -> IntSet.add i acc
  | Miniml.Tarr (t1, t2) -> collect_tvars_set (collect_tvars_set acc t1) t2
  | Miniml.Tglob (_, args, _) -> List.fold_left collect_tvars_set acc args
  | Miniml.Tmeta {contents = Some t} -> collect_tvars_set acc t
  | _ -> acc

(** Convert an IntSet of type variable indices back to a list, wrapping
    [collect_tvars_set]. Used to collect all Tvar indices from an ml_type. *)
let collect_tvars acc ty =
  IntSet.elements (collect_tvars_set (IntSet.of_list acc) ty)

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

(** True if a C++ type represents an erased parameter — either Tany (from an
    unresolved Tmeta in the ML AST) or a dummy_type glob (from Tdummy). When any
    type arg in a template argument list is erased, ALL explicit type args must
    be dropped (see filter_erased_type_args). *)
let is_erased_type t = t = Minicpp.Tany || is_cpp_dummy_type t

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
  | Tfun (dom, cod) -> List.exists has_tany_in_type dom || has_tany_in_type cod
  | Tmod (_, t) -> has_tany_in_type t
  | Tshared_ptr t -> has_tany_in_type t
  | Tunique_ptr t -> has_tany_in_type t
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
let filter_erased_type_args tys =
  (* Phase 1: Strip proof-erasure markers *)
  let tys = List.filter (fun t -> not (is_cpp_dummy_prop t)) tys in
  (* Phase 2: Apply all-or-nothing rule for erased types *)
  if List.exists is_erased_type tys then [] else tys

(** Recursively check whether a C++ type tree contains erased HKT markers (Tany
    or dummy_type globs). These markers arise when a higher-kinded type
    constructor (e.g., F : Type -> Type) is erased during extraction — the type
    constructor itself becomes Tany/dummy_type, but it may be nested inside a
    function type like (A -> B) -> F A -> F B. Used by gen_dfun and
    gen_decl_for_pp to detect function params whose type variables cannot be
    deduced by C++ and should therefore use plain TTtypename instead of a MapsTo
    constraint. *)
let rec has_hkt_erasure = function
  | Minicpp.Tany -> true
  | t when is_cpp_dummy_type t -> true
  | Minicpp.Tfun (d, c) -> List.exists has_hkt_erasure d || has_hkt_erasure c
  | Minicpp.Tmod (_, t)
   |Minicpp.Tref t
   |Minicpp.Tshared_ptr t
   |Minicpp.Tunique_ptr t
   |Minicpp.Tnamespace (_, t) -> has_hkt_erasure t
  | Minicpp.Tglob (_, ts, _) | Minicpp.Tvariant ts ->
    List.exists has_hkt_erasure ts
  | _ -> false

(** Collect all Tvar indices from an ML AST, using collect_tvars on embedded
    types. Used to find all type variables referenced in a function body. *)
let rec collect_tvars_ast acc = function
  | MLlam (_, ty, body) -> collect_tvars_ast (collect_tvars acc ty) body
  | MLletin (_, ty, a, b) ->
    collect_tvars_ast (collect_tvars_ast (collect_tvars acc ty) a) b
  | MLglob (_, tys) -> List.fold_left collect_tvars acc tys
  | MLcons (ty, _, args) ->
    List.fold_left collect_tvars_ast (collect_tvars acc ty) args
  | MLcase (ty, e, brs) ->
    let acc = collect_tvars_ast (collect_tvars acc ty) e in
    Array.fold_left
      (fun acc (ids, ty, _, body) ->
        let acc =
          List.fold_left (fun acc (_, t) -> collect_tvars acc t) acc ids
        in
        collect_tvars_ast (collect_tvars acc ty) body )
      acc
      brs
  | MLfix (_, ids, funs, _) ->
    let acc =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) acc ids
    in
    Array.fold_left collect_tvars_ast acc funs
  | MLapp (f, args) ->
    List.fold_left collect_tvars_ast (collect_tvars_ast acc f) args
  | MLmagic a -> collect_tvars_ast acc a
  | MLparray (arr, def) ->
    collect_tvars_ast (Array.fold_left collect_tvars_ast acc arr) def
  | MLtuple args -> List.fold_left collect_tvars_ast acc args
  | MLrel _
   |MLexn _
   |MLdummy _
   |MLaxiom _
   |MLuint _
   |MLfloat _
   |MLstring _ -> acc

(** True when evaluating an ML AST may throw through an extracted axiom or
    exception. Functions whose bodies can throw must not be marked
    [__attribute__((pure))]: Clang may otherwise move calls across local
    exception handlers or discard them when their result is unused. *)
let rec ast_may_throw = function
  | MLaxiom _ | MLexn _ -> true
  | MLglob (r, _) -> Table.is_axiom_value r
  | MLlam (_, _, body) -> ast_may_throw body
  | MLletin (_, _, a, b) -> ast_may_throw a || ast_may_throw b
  | MLcons (_, _, args) -> List.exists ast_may_throw args
  | MLcase (_, e, brs) ->
    ast_may_throw e
    || Array.exists (fun (_, _, _, body) -> ast_may_throw body) brs
  | MLfix (_, _, funs, _) -> Array.exists ast_may_throw funs
  | MLapp (f, args) -> ast_may_throw f || List.exists ast_may_throw args
  | MLmagic a -> ast_may_throw a
  | MLparray (arr, def) -> Array.exists ast_may_throw arr || ast_may_throw def
  | MLtuple args -> List.exists ast_may_throw args
  | MLrel _ | MLdummy _ | MLuint _ | MLfloat _ | MLstring _ -> false

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

(** Build Tvar i -> concrete_type substitution by unifying two ML types
    structurally. Walks both types in parallel; when one side has Tvar i and the
    other has a concrete type, records the mapping. Conflicting mappings are
    discarded. *)
let build_tvar_subst_from_unify ty_with_tvars ty_concrete =
  let seen = Hashtbl.create 8 in
  let rec unify t1 t2 =
    match (t1, t2) with
    | (Miniml.Tvar i | Miniml.Tvar' i), _ when not (has_tvar t2) ->
      ( match Hashtbl.find_opt seen i with
      | None -> Hashtbl.replace seen i (Some t2)
      | Some (Some _) -> Hashtbl.replace seen i None
      | Some None -> () )
    | _, (Miniml.Tvar i | Miniml.Tvar' i) when not (has_tvar t1) ->
      ( match Hashtbl.find_opt seen i with
      | None -> Hashtbl.replace seen i (Some t1)
      | Some (Some _) -> Hashtbl.replace seen i None
      | Some None -> () )
    | Miniml.Tarr (a1, b1), Miniml.Tarr (a2, b2) ->
      unify a1 a2;
      unify b1 b2
    | Miniml.Tglob (_, args1, _), Miniml.Tglob (_, args2, _)
      when List.length args1 = List.length args2 -> List.iter2 unify args1 args2
    | Miniml.Tmeta {contents = Some t}, other
     |other, Miniml.Tmeta {contents = Some t} -> unify t other
    | _ -> ()
  in
  unify ty_with_tvars ty_concrete;
  Hashtbl.fold
    (fun i v acc ->
      match v with
      | Some ty -> (i, ty) :: acc
      | None -> acc )
    seen
    []

(** Collect all types that should be unified with the top-level function type.
    Returns a list of types to unify pairwise with the top-level type:
    - The arrow type reconstructed from MLlam annotations
    - The type annotation on the MLfix binding (if present)
    - The arrow type from the MLfix's inner function body *)
let collect_body_types_for_unify body =
  let types = ref [] in
  let rec from_lams = function
    | MLlam (_, ty, inner) -> Miniml.Tarr (ty, from_lams inner)
    | MLfix (_, ids, funs, _) ->
      Array.iter (fun (_, ty) -> types := ty :: !types) ids;
      Array.iter (fun f -> types := from_lams f :: !types) funs;
      Miniml.Tunknown
    | _ -> Miniml.Tunknown
  in
  let outer = from_lams body in
  outer :: !types

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

(** Resolve Tvars in the body by unifying body type annotations with the
    top-level type. Only applied when the top-level type is fully concrete (no
    Tvars, no unresolved metas). Returns the (possibly substituted) body. *)
let resolve_body_tvars b ty =
  let ty = type_simpl ty in
  if has_tvar ty then
    b (* top-level type is polymorphic, don't touch the body *)
  else
    let body_types = collect_body_types_for_unify b in
    let tvar_subst =
      List.concat_map (fun bt -> build_tvar_subst_from_unify bt ty) body_types
    in
    let tvar_subst =
      List.fold_left
        (fun acc (i, t) -> if List.mem_assoc i acc then acc else (i, t) :: acc)
        []
        tvar_subst
    in
    match tvar_subst with
    | [] -> b
    | _ -> map_types_in_ast (subst_tvars_type tvar_subst) b

(** Resolve all unresolved type meta-variables in an [ml_type] to fresh
    [Tvar]s. Each [Tmeta {contents = None}] encountered gets unified (via
    [try_mgu]) with [Tvar idx], where [idx] is drawn from [next_tvar] and
    incremented. Chases [Tmeta {contents = Some t}]. Recurses into [Tarr]
    and [Tglob] args. *)
let rec resolve_type_metas ~next_tvar = function
  | Miniml.Tmeta ({contents = None} as m) ->
    let idx = !next_tvar in
    next_tvar := idx + 1;
    try_mgu (Miniml.Tmeta m) (Miniml.Tvar idx)
  | Miniml.Tmeta {contents = Some t} -> resolve_type_metas ~next_tvar t
  | Miniml.Tarr (t1, t2) ->
    resolve_type_metas ~next_tvar t1;
    resolve_type_metas ~next_tvar t2
  | Miniml.Tglob (_, args, _) -> List.iter (resolve_type_metas ~next_tvar) args
  | _ -> ()

(** Resolve unresolved metas in an ML AST by walking its sub-types.
    resolve_metas should be a function that resolves metas in a single ml_type.
*)
let rec resolve_metas_in_ast resolve_metas = function
  | MLlam (_, ty, body) ->
    resolve_metas ty;
    resolve_metas_in_ast resolve_metas body
  | MLletin (_, ty, a, b) ->
    resolve_metas ty;
    resolve_metas_in_ast resolve_metas a;
    resolve_metas_in_ast resolve_metas b
  | MLglob (_, tys) -> List.iter resolve_metas tys
  | MLcons (ty, _, args) ->
    resolve_metas ty;
    List.iter (resolve_metas_in_ast resolve_metas) args
  | MLcase (ty, e, brs) ->
    resolve_metas ty;
    resolve_metas_in_ast resolve_metas e;
    Array.iter
      (fun (ids, ty, _, body) ->
        List.iter (fun (_, t) -> resolve_metas t) ids;
        resolve_metas ty;
        resolve_metas_in_ast resolve_metas body )
      brs
  | MLfix (_, ids, funs, _) ->
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    Array.iter (resolve_metas_in_ast resolve_metas) funs
  | MLapp (f, args) ->
    resolve_metas_in_ast resolve_metas f;
    List.iter (resolve_metas_in_ast resolve_metas) args
  | MLmagic a -> resolve_metas_in_ast resolve_metas a
  | MLparray (arr, def) ->
    Array.iter (resolve_metas_in_ast resolve_metas) arr;
    resolve_metas_in_ast resolve_metas def
  | MLtuple args -> List.iter (resolve_metas_in_ast resolve_metas) args
  | MLrel _
   |MLexn _
   |MLdummy _
   |MLaxiom _
   |MLuint _
   |MLfloat _
   |MLstring _ -> ()

(** Substitute [CPPvar target] with [repl] in expressions and statements. Uses
    generic AST visitors for structural recursion. *)
let rec local_var_subst_expr (target : Id.t) (repl : cpp_expr) (e : cpp_expr) =
  match e with
  | CPPvar id when Id.equal id target -> repl
  | _ ->
    map_expr
      (local_var_subst_expr target repl)
      (local_var_subst_stmt target repl)
      Fun.id
      e

(** Statement-level counterpart of [local_var_subst_expr]: substitute
    [CPPvar target] with [repl] inside a single C++ statement. *)
and local_var_subst_stmt (target : Id.t) (repl : cpp_expr) (s : cpp_stmt) =
  map_stmt
    (local_var_subst_expr target repl)
    (local_var_subst_stmt target repl)
    Fun.id
    s

(** Check whether a variable [target] is referenced in a list of C++ stmts. *)
let stmts_reference_var (target : Id.t) (stmts : cpp_stmt list) : bool =
  let exception Found in
  let rec visit_expr e =
    ( match e with
    | CPPvar id when Id.equal id target -> raise Found
    | _ -> () );
    map_expr visit_expr visit_stmt Fun.id e
  and visit_stmt s =
    map_stmt visit_expr visit_stmt Fun.id s
  in
  try List.iter (fun s -> ignore (visit_stmt s)) stmts; false
  with Found -> true

(** Check if [target] is referenced DIRECTLY in [stmts], without crossing into
    lambda bodies. References inside [CPPlambda] bodies are excluded because
    Infer's Pulse analysis cannot trace reads through [std::visit] lambda
    captures — they appear as dead stores even when the variable is used. *)
let stmts_reference_var_directly (target : Id.t) (stmts : cpp_stmt list) : bool =
  let exception Found in
  let rec ve = function
    | CPPvar id when Id.equal id target -> raise Found
    | CPPlambda _ -> ()  (* Don't recurse into lambda bodies *)
    | CPPfun_call (f, args) -> ve f; List.iter ve args
    | CPPnamespace (_, e) | CPPderef e | CPPmove e | CPPforward (_, e) -> ve e
    | CPPget (e, _) | CPPget' (e, _) | CPPmember (e, _) | CPParrow (e, _) -> ve e
    | CPPqualified (e, _) | CPPshared_ptr_ctor (_, e) | CPPunique_ptr_ctor (_, e) -> ve e
    | CPPany_cast (_, e) -> ve e
    | CPPshared_from_this _ -> ()
    | CPPoverloaded es | CPPstructmk (_, _, es) | CPPstruct (_, _, es)
    | CPPstruct_id (_, _, es) | CPPnew (_, es) -> List.iter ve es
    | CPPparray (arr, e) -> Array.iter ve arr; ve e
    | CPPmethod_call (obj, _, args) -> ve obj; List.iter ve args
    | CPPrequires (_, constraints, _) -> List.iter (fun (e, _) -> ve e) constraints
    | CPPbinop (_, l, r) -> ve l; ve r
    | CPPunop (_, e) -> ve e
    | CPPvar _ | CPPglob _ | CPPvisit | CPPmk_shared _ | CPPmk_unique _ | CPPstring _
    | CPPuint _ | CPPfloat _ | CPPconvertible_to _ | CPPabort _ | CPPenum_val _
    | CPPraw _ | CPPbool _ | CPPint _ | CPPbrace_init | CPPthis -> ()
  and vs = function
    | Sreturn (Some e) | Sexpr e -> ve e
    | Sreturn None | Sdecl _ | Sthrow _ | Sassert _ | Sraw _ | Sstruct_def _
    | Susing _ | Sdecl_init _ | Scontinue | Sbreak -> ()
    | Sasgn (_, _, e) | Sderef_asgn (_, e) -> ve e
    | Sif (c, t, f) -> ve c; List.iter vs t; List.iter vs f
    | Sswitch (e, _, branches, def) ->
      ve e;
      List.iter (fun (_, stmts) -> List.iter vs stmts) branches;
      Option.iter (List.iter vs) def
    | Scustom_case (_, e, _, branches, _) ->
      ve e;
      List.iter (fun (_, _, stmts) -> List.iter vs stmts) branches
    | Sassign_field (o, _, e) -> ve o; ve e
    | Swhile (c, stmts) -> ve c; List.iter vs stmts
    | Sblock stmts -> List.iter vs stmts
    | Sblock_custom (_, _, _, _, args, _) -> List.iter ve args
    | Smatch (branches, default) ->
      List.iter (fun br ->
        ve br.smb_scrutinee;
        List.iter ve br.smb_extra_conds;
        ( match br.smb_reuse with
        | Some (cond, _, stmts) -> ve cond; List.iter vs stmts
        | None -> () );
        List.iter vs br.smb_body) branches;
      Option.iter (List.iter vs) default
  in
  try List.iter vs stmts; false
  with Found -> true

(** Build type variable names for a list of Tvar indices. Indices within
    [n_outer] reuse names from [outer_tvars]; indices beyond get fresh
    [tvar_id i] names. Converts [outer_tvars] to an array for O(1) lookup. *)
let build_tvar_names ~outer_tvars tvar_indices =
  let n_outer = List.length outer_tvars in
  let outer_arr = Array.of_list outer_tvars in
  List.map
    (fun i ->
      if i <= n_outer then outer_arr.(i - 1) else tvar_id i)
    tvar_indices

(** Build extended tvar names covering both signature and body Tvar indices.
    sig_indices: sorted list of Tvar indices from the function signature
    sig_names: corresponding Id.t names for those indices body_tvars:
    sorted-unique list of all Tvar indices found in the body *)
let build_extended_tvar_names sig_indices sig_names body_tvars =
  let n_sig = List.length sig_indices in
  let sig_set = IntSet.of_list sig_indices in
  let body_extra_tvars =
    List.filter (fun i -> not (IntSet.mem i sig_set)) body_tvars
  in
  let max_tvar = List.fold_left max 0 (sig_indices @ body_tvars) in
  let tvar_name_map =
    List.map2 (fun i name -> (i, name)) sig_indices sig_names
  in
  let tvar_name_map =
    if body_extra_tvars <> [] then
      let min_sig = List.hd sig_indices in
      let min_extra = List.fold_left min max_int body_extra_tvars in
      let offset = min_extra - min_sig in
      List.fold_left
        (fun acc i ->
          let mapped_sig_idx = i - offset in
          if mapped_sig_idx >= 1 && mapped_sig_idx <= n_sig then
            let name = List.assoc mapped_sig_idx tvar_name_map in
            (i, name) :: acc
          else
            (i, tvar_id i) :: acc )
        tvar_name_map
        body_extra_tvars
    else
      tvar_name_map
  in
  if max_tvar > 0 then
    List.init max_tvar (fun i ->
      let idx = i + 1 in
      match List.assoc_opt idx tvar_name_map with
      | Some name -> name
      | None -> anon_tvar_id idx )
  else
    sig_names

(* Walk an ML AST and collect source-order parameter indices that are NOT
   simply forwarded unchanged at recursive call sites.  [is_self_call depth f]
   returns true when the head [f] of an application is a self-recursive
   reference at the given binder depth.

   After collect_lams, param source index [i] has de Bruijn index
   [n_params - i] at depth 0, shifted by [depth] under binders. *)
let detect_non_forwarded_params_generic ~is_self_call n_params body =
  let non_fwd = Hashtbl.create 4 in
  let is_forwarded depth i arg =
    let expected_db = n_params - i + depth in
    match arg with
    | MLmagic (MLrel db) | MLrel db -> db = expected_db
    | _ -> false
  in
  let rec walk depth = function
    | MLapp (f, args) when is_self_call depth f ->
      List.iteri
        (fun i arg ->
          if i < n_params && not (is_forwarded depth i arg) then
            Hashtbl.replace non_fwd i true )
        args
    | MLapp (f, args) ->
      walk depth f;
      List.iter (walk depth) args
    | MLlam (_, _, body) -> walk (depth + 1) body
    | MLletin (_, _, e1, e2) ->
      walk depth e1;
      walk (depth + 1) e2
    | MLcase (_, scrut, branches) ->
      walk depth scrut;
      Array.iter
        (fun (ids, _, _, body) ->
          walk (depth + List.length ids) body )
        branches
    | MLcons (_, _, args) -> List.iter (walk depth) args
    | MLtuple args -> List.iter (walk depth) args
    | MLfix (_, _, bodies, _) ->
      let n = Array.length bodies in
      Array.iter (walk (depth + n)) bodies
    | MLmagic e -> walk depth e
    | MLparray (elts, def) ->
      Array.iter (walk depth) elts;
      walk depth def
    | MLrel _
     |MLglob _
     |MLexn _
     |MLdummy _
     |MLaxiom _
     |MLuint _
     |MLfloat _
     |MLstring _ -> ()
  in
  walk 0 body;
  Hashtbl.fold (fun k _ acc -> k :: acc) non_fwd []

(* Detect non-forwarded params in a local fixpoint body.  Self-references
   use MLrel: after collect_lams strips [n_params] lambda params, the fix
   binding for [fix_idx] in [n_fix] mutual funs is at
   db = [n_params + n_fix - fix_idx], shifted by binder depth. *)
let detect_non_forwarded_params_fix n_params n_fix fix_idx body =
  let base_self_db = n_params + n_fix - fix_idx in
  detect_non_forwarded_params_generic
    ~is_self_call:(fun depth -> function
      | MLrel db -> db = base_self_db + depth
      | _ -> false )
    n_params body

(** Convert ML params to C++ types with const/ref wrapping, and create
    forwarding-ref template parameters for function-typed params. convert_fn:
    function to convert ml_type -> cpp_type (typically
    convert_ml_type_to_cpp_type env Refset'.empty tvar_names) Returns
    (cpp_params, all_temps_with_funs). *)
let build_lifted_cpp_params ?(non_fwd_source_indices = []) convert_fn base_temps params =
  let n_total = List.length params in
  (* Non-forwarded check in source order (for fun_tys, which iterates List.rev) *)
  let is_non_fwd_source j = List.mem j non_fwd_source_indices in
  (* Non-forwarded check in de Bruijn order (for cpp_params replacement) *)
  let is_non_fwd_db j = List.mem (n_total - 1 - j) non_fwd_source_indices in
  let cpp_params =
    List.map
      (fun (id, ty) ->
        let cpp_ty = convert_fn ty in
        match cpp_ty with
        | Tshared_ptr _ -> (id, Tref (Tmod (TMconst, cpp_ty)))
        | _ -> (id, Tmod (TMconst, cpp_ty)) )
      params
  in
  let fun_tys =
    List.filter_map
      (fun (x, ty, j) ->
        match ty with
        | Tmod (TMconst, Tfun (dom, cod_f)) when not (is_non_fwd_source j) ->
          let cod_f = if is_cpp_unit_type cod_f then Tvoid else cod_f in
          Some (x, TTfun (dom, cod_f), fun_tparam_id j)
        | _ -> None )
      (List.mapi (fun j (x, ty) -> (x, ty, j)) (List.rev cpp_params))
  in
  let n_params = List.length cpp_params in
  let cpp_params =
    List.mapi
      (fun j (x, ty) ->
        match ty with
        | Tmod (TMconst, Tfun (_, _)) when not (is_non_fwd_db j) ->
          (x, Tref (Tref (Tvar (0, Some (fun_tparam_id (n_params - j - 1))))))
        | _ -> (x, ty) )
      cpp_params
  in
  let extra_temps = List.map (fun (_, t, n) -> (t, n)) fun_tys in
  let all_temps_with_funs = base_temps @ extra_temps in
  (cpp_params, all_temps_with_funs)

(** Extract return type from a function type, stripping all Tarr layers. *)
let rec ml_return_type = function
  | Tarr (_, rest) -> ml_return_type rest
  | t -> t

(** Extract argument types and return type from a function type. *)
let rec get_args_and_ret acc = function
  | Tarr (t, rest) -> get_args_and_ret (t :: acc) rest
  | ret_ty -> (List.rev acc, ret_ty)

(** Check if a GlobRef returns a typeclass type (possibly through Tarr layers).
*)
let ref_returns_typeclass r =
  match find_type_opt r with
  | Some ty -> Table.is_typeclass_type (ml_return_type ty)
  | None -> false

(** Check if a function returns a skipped type (e.g., ReSum instances whose
    Class is extracted as a ConstRef, not IndRef, and thus not recognized by
    [is_typeclass]). Such arguments are infrastructure that should be erased. *)
let ref_returns_skipped r =
  match find_type_opt r with
  | Some ty ->
    ( match ml_return_type ty with
    | Tglob (rr, _, _) ->
      Table.is_inline_custom rr && Table.find_custom_opt rr = Some ""
    | _ -> false )
  | None -> false

(* Use Common.extract_at_pos for extracting elements at a position *)

(** Create a substitution function for extra type variables in C++ types.
    num_ind_vars: number of type vars from the containing inductive/record
    extra_tvar_map: mapping from Tvar index to Id for extra type vars *)
let make_subst_extra_tvars num_ind_vars extra_tvar_map =
  let rec subst = function
    | Tvar (i, None) when List.mem_assoc i extra_tvar_map ->
      Tvar (0, Some (List.assoc i extra_tvar_map))
    | Tvar (i, None) when i >= 1 && i <= num_ind_vars ->
      (* Inductive's type var - keep as-is for tvar_subst_stmt *)
      Tvar (i, None)
    | Tfun (dom, cod) -> Tfun (List.map subst dom, subst cod)
    | Tshared_ptr t -> Tshared_ptr (subst t)
    | Tunique_ptr t -> Tunique_ptr (subst t)
    | Tglob (r, args, e) -> Tglob (r, List.map subst args, e)
    | Tref t -> Tref (subst t)
    | Tmod (m, t) -> Tmod (m, subst t)
    | Tvariant tys -> Tvariant (List.map subst tys)
    | Tnamespace (r, t) -> Tnamespace (r, subst t)
    | Tqualified (t, id) -> Tqualified (subst t, id)
    | t -> t
  in
  subst

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
  | Tunique_ptr ty -> Tunique_ptr (tvar_erase_type ty)
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
  | Tunique_ptr ty -> has_unnamed_tvar ty
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

(** Collect de Bruijn indices of free variables in an ML AST. n_bound is the
    number of locally bound variables (lambda params, let bindings, etc.).
    Returns indices relative to the outer scope (i.e., i - n_bound for each free
    MLrel i). *)
let rec collect_free_rels_set n_bound acc = function
  | MLrel i -> if i > n_bound then IntSet.add (i - n_bound) acc else acc
  | MLlam (_, _, body) -> collect_free_rels_set (n_bound + 1) acc body
  | MLletin (_, _, a, b) ->
    collect_free_rels_set n_bound (collect_free_rels_set (n_bound + 1) acc b) a
  | MLapp (f, args) ->
    List.fold_left
      (collect_free_rels_set n_bound)
      (collect_free_rels_set n_bound acc f)
      args
  | MLcase (_, e, brs) ->
    let acc = collect_free_rels_set n_bound acc e in
    Array.fold_left
      (fun acc (ids, _, _, body) ->
        collect_free_rels_set (n_bound + List.length ids) acc body )
      acc
      brs
  | MLfix (_, ids, funs, _) ->
    let n_fix = Array.length ids in
    Array.fold_left
      (fun acc f ->
        let params, body = collect_lams f in
        collect_free_rels_set (n_bound + List.length params + n_fix) acc body )
      acc
      funs
  | MLcons (_, _, args) ->
    List.fold_left (collect_free_rels_set n_bound) acc args
  | MLmagic a -> collect_free_rels_set n_bound acc a
  | MLtuple args -> List.fold_left (collect_free_rels_set n_bound) acc args
  | MLparray (arr, def) ->
    collect_free_rels_set
      n_bound
      (Array.fold_left (collect_free_rels_set n_bound) acc arr)
      def
  | MLglob _
   |MLexn _
   |MLdummy _
   |MLaxiom _
   |MLuint _
   |MLfloat _
   |MLstring _ -> acc

(** Collect all free de Bruijn variables (rels) from an ML AST, wrapping
    [collect_free_rels_set]. Used to detect which lambda parameters are
    captured. *)
let collect_free_rels n_bound body =
  IntSet.elements (collect_free_rels_set n_bound IntSet.empty body)

(** Check if a C++ type is a non-trivial value type (inductive struct),
    meaning it should be passed by value when owned and by const ref when
    borrowed, rather than by const value like primitives. *)
let is_inductive_value_type = function
  | Tglob (g, _, _) | Tnamespace (g, _) -> (
    match g with
    | GlobRef.IndRef _ ->
      not (is_enum_inductive g)
      && not (Table.is_coinductive g)
    | _ -> false )
  | _ -> false

(** Wraps a C++ parameter type with const/ref based on ownership semantics.
    Owned inductive/shared_ptr params are passed by value (moved in);
    borrowed inductive/shared_ptr/unique_ptr params are passed by const
    reference; other types are passed by const value. *)
let wrap_param_by_ownership ?(is_owned = false) cpp_ty =
  match cpp_ty with
  | Tshared_ptr _ when is_owned -> cpp_ty
  | Tshared_ptr _ | Tunique_ptr _ -> Tref (Tmod (TMconst, cpp_ty))
  | _ when is_inductive_value_type cpp_ty ->
    if is_owned then cpp_ty  (* pass by value, caller moves *)
    else Tref (Tmod (TMconst, cpp_ty))  (* const T& for borrowing *)
  | _ -> Tmod (TMconst, cpp_ty)

(** Check if the return type of an ML function type is erased — i.e., it
    becomes [std::any] in C++.  This covers three cases:
    - Promoted type vars (erased carrier projections like [Obj C]).
    - [Tunknown] arising from dependent type families.
    - Erased type constants — non-promoted type-valued record fields
      (e.g. [Hom : Obj -> Obj -> Type] in [PreCategory]) registered during
      extraction via {!Table.add_erased_type_const}. *)
let rec ml_return_type_is_erased = function
  | Miniml.Tarr (_, ret) -> ml_return_type_is_erased ret
  | Miniml.Tmeta { contents = Some t } -> ml_return_type_is_erased t
  | Miniml.Tglob (g, _, _) when Table.is_promoted_type_var g -> true
  | Miniml.Tglob (g, _, _) when Table.is_erased_type_const g -> true
  | Miniml.Tunknown -> true
  | _ -> false

(** Check if an ML expression is (or starts with) a record field projection
    whose projected field returns a promoted type var (erased to [std::any] in
    C++).  This detects the gap between Coq-level types and C++ types that
    arises when a record like [Functor] uses erased carriers ([Obj = std::any])
    in its field types.

    For example, [object_of forward_functor 7] is an [MLapp] wrapping an
    [MLcase] record projection.  The projected field [object_of] has ML type
    [carrier → carrier] whose return type [carrier] is a promoted var.  The
    Coq type says the result is [nat = unsigned int], but the C++ expression
    [forward_functor->object_of(7u)] actually returns [std::any]. *)
let rec ml_body_returns_erased_field = function
  | Miniml.MLapp (f, _) -> ml_body_returns_erased_field f
  | MLmagic f -> ml_body_returns_erased_field f
  | MLcase (typ, _, pv) when Array.length pv = 1 ->
    let ids, _, _, proj_body = pv.(0) in
    let n = List.length ids in
    let proj_idx =
      match proj_body with
      | MLrel i when i >= 1 && i <= n -> Some (n - i)
      | MLmagic (MLrel i) when i >= 1 && i <= n -> Some (n - i)
      | MLapp (MLrel i, _) when i >= 1 && i <= n -> Some (n - i)
      | MLapp (MLmagic (MLrel i), _) when i >= 1 && i <= n -> Some (n - i)
      | _ -> None
    in
    ( match proj_idx with
    | Some idx -> (
      match typ with
      | Tglob (r, _, _) ->
        let all_field_types = Table.record_field_types r in
        let non_erased =
          filter_value_types all_field_types
        in
        ( try
            let field_ty = List.nth non_erased idx in
            ml_return_type_is_erased field_ty
          with _ -> false )
      | _ -> false )
    | None -> false )
  | _ -> false

(** Check if the head of an ML application has an [MLmagic] wrapper.

    The [simpl] optimization in {!Mlutil} transforms
    [MLmagic(MLapp(f, args))] into [MLapp(MLmagic(f), args)], pushing magic
    inside application heads.  A top-level [MLmagic] check therefore misses
    these cases.  This function follows application heads recursively.

    Used in {!gen_spec} to detect when a function call's result needs a C++
    cast to match the expected return type. *)
let rec ml_head_has_magic = function
  | Miniml.MLmagic _ -> true
  | MLapp (f, _) -> ml_head_has_magic f
  | _ -> false

(** Does a C++ type mention [unique_ptr] or [shared_ptr] anywhere in its
    structure?  Used to decide whether a field-type / bare-type mismatch in
    pattern matching is real (pointer wrapping) vs. superficial (namespace). *)
let rec contains_shared_ptr_or_unique_ptr = function
  | Tshared_ptr _ | Tunique_ptr _ -> true
  | Tref t | Tmod (_, t) | Tptr t -> contains_shared_ptr_or_unique_ptr t
  | Tid (_, args) | Tid_external (_, args) | Tglob (_, args, _) ->
    List.exists contains_shared_ptr_or_unique_ptr args
  | Tnamespace (_, t) -> contains_shared_ptr_or_unique_ptr t
  | Tfun (args, ret) ->
    List.exists contains_shared_ptr_or_unique_ptr args
    || contains_shared_ptr_or_unique_ptr ret
  | _ -> false

(** Wrap [expr] when [storage_ty] and [api_ty] differ due to pointer
    wrapping.  Converts from API form to storage form (e.g. bare value →
    [unique_ptr]).  No-op when the types match or neither involves smart
    pointers. *)
let wrap_storage_expr ~storage_ty ~api_ty expr =
  if storage_ty <> api_ty && contains_shared_ptr_or_unique_ptr storage_ty then
    gen_clone_field_expr ~src_ty:api_ty ~dst_ty:storage_ty expr
  else
    expr

(** Like {!wrap_storage_expr} but converts from storage form to API form
    (e.g. [unique_ptr] → bare value). *)
let wrap_api_expr ~storage_ty ~api_ty expr =
  if storage_ty <> api_ty && contains_shared_ptr_or_unique_ptr storage_ty then
    gen_clone_field_expr ~src_ty:storage_ty ~dst_ty:api_ty expr
  else
    expr

(** Convert ML type to C++ type. Handles custom types, inductives, type
    variables, and erased parameters. env: variable environment; ns: set of
    local references; tvars: type variable names *)
let rec convert_ml_type_to_cpp_type
    env
    (ns : Refset'.t)
    (tvars : Id.t list)
    (ml_t : ml_type) : cpp_type =
  (* [ns] is the only source of recursive-storage wrapping.  Public API
     conversions pass an empty [ns], so types like [List<tree>] stay value
     shaped in function signatures.  Struct-field storage conversion passes the
     owning inductive in [ns], so recursive occurrences at constructor storage
     sites become [unique_ptr]. *)
  match ml_t with
  | Tarr (t1, t2) ->
    let t1c = convert_ml_type_to_cpp_type env ns tvars t1 in
    (* Reify monadic domain types: itree E R in parameter position becomes
       shared_ptr<ITree<R>> so the tree can be passed as a value. *)
    let t1c = reify_monadic_param_type t1 t1c in
    let t2c = convert_ml_type_to_cpp_type env ns tvars t2 in
    (* Skip erased params: isTdummy catches direct Tdummy, is_cpp_dummy_type
       catches Tdummy wrapped in Tmeta (e.g., Tmeta{contents=Some(Tdummy Kprop)}
       which converts to dummy_prop glob). Do NOT use is_erased_type here as it
       also catches Tany (std::any), which is a valid type for universally
       quantified parameters — stripping it would incorrectly collapse (A -> IO)
       into just IO. *)
    if isTdummy t1 || is_cpp_dummy_type t1c then
      t2c
    else (
      (* Void-ify unit codomain: function types returning [unit] (directly
         or via monadic wrapper like [itree E unit]) should map to [void]
         to match void-ified function definitions. Check the ML type [t2]
         since the C++ type may still be a monad Tglob, not bare unit. *)
      let voidify_cod c =
        if is_cpp_unit_type c then Tvoid
        else if ml_type_is_unit (ml_result_type t2) then Tvoid
        else c
      in
      match
        t2c
      with
      | Tfun (l, t) -> Tfun (t1c :: l, voidify_cod t)
      | _ -> Tfun (t1c :: [], voidify_cod t2c) )
  | Tglob (g, _, _) when is_void g -> Tvoid
  (* PROMOTED TYPE VARIABLES: Handle references to record fields that were
     "promoted" from value-level fields to type-level parameters.

     A "promoted" field is a Type-valued record field (e.g., [m_carrier : Type]
     in [Record Monoid]) that became a C++ concept type requirement instead of
     a struct field. At usage sites, references to these fields must be treated
     as TYPES, not values.

     Example:
       Coq: [mfold (M : Monoid) (l : list (m_carrier M))]
            Here [m_carrier M] is a TYPE (the carrier type of the monoid M)

       C++: [template <Monoid _tcI0> ... List<typename _tcI0::m_carrier> ...]
            Must qualify as a type, not access as a field: NOT _tcI0->m_carrier

     Three contexts for promoted type vars:
     1. Inside template functions with typeclass params: [promoted_var_map] is
        populated, resolve to qualified types like [typename _tcI0::m_carrier]
     2. Module-level (constructor expressions): Use module aliases ([std::any])
     3. No context: Mark with [Tvar(1000, ...)] for later resolution *)
  | Tglob (g, ts, _) when Table.is_promoted_type_var g ->
    ( match Table.promoted_type_var_name g with
    | Some var_id ->
      (match
        List.find_opt
          (fun (n, _) -> Id.equal n var_id)
          tctx.promoted_var_map
      with
      | Some (_, resolved) -> resolved
      | None ->
        (* No resolution found.  When the constructor-expression flag is set,
           all promoted vars become [Tany] (= std::any) because module-level
           type aliases are always std::any and non-Type promoted vars (like
           [base_category]) have no alias at all.  Otherwise keep the marker
           for concept generation and signature printing. *)
        if tctx.in_constructor_expr then Tany
        else Tvar (1000, Some var_id) )
    | None -> Tany )
  | Tglob (g, ts, args) when is_custom g ->
    Tglob
      ( g,
        List.map (convert_ml_type_to_cpp_type env ns tvars) ts,
        List.map (gen_expr env) args )
  | Tglob (g, ts, _) ->
    (* For inductives, only keep type args that correspond to parameters (not
       indices). Parameters become template params in C++; indices are
       erased. *)
    let filtered_ts =
      match g with
      | GlobRef.IndRef (kn, _) ->
        (* Filter type args to keep only parameters (not indices). Use
           get_ind_num_param_vars_opt to determine how many to keep. For
           local/self-references with non-empty tvars, we can use tvars length
           as a fallback, but prefer the table lookup for accuracy. *)
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars ->
          (* Only keep the first num_param_vars type args - the rest are
             indices *)
          safe_firstn num_param_vars ts
        | None ->
          (* Fallback: if tvars is non-empty and this is a local reference, use
             tvars length *)
          let is_local =
            Refset'.mem g ns
            || List.exists
                 (Environ.QGlobRef.equal Environ.empty_env g)
                 !local_inductives
          in
          if is_local && tvars <> [] then
            safe_firstn (List.length tvars) ts
          else
            ts )
        (* Keep all if we can't determine *)
      | _ -> ts
    in
    (* Only propagate ns into type arguments when g itself is a self-ref.
       For non-self types (e.g. list inside tree's definition), type args
       stay bare — the field-level wrapping handles the cycle-breaking.
       This ensures type variables are never unique_ptr at instantiation. *)
    let ns_for_args =
      if Refset'.mem g ns then ns else Refset'.empty
    in
    let converted_ts =
      List.map (convert_ml_type_to_cpp_type env ns_for_args tvars) filtered_ts
    in
    let core = Tglob (g, converted_ts, []) in
    ( match g with
    | GlobRef.IndRef _ ->
      (* Enum inductives are value types - no shared_ptr wrapping *)
      if is_enum_inductive g then
        let is_local =
          Refset'.mem g ns
          || List.exists
               (Environ.QGlobRef.equal Environ.empty_env g)
               !local_inductives
        in
        if is_local then
          core
        else
          Tnamespace (g, core)
      else
        (* Check if this inductive is in the explicit ns list or in
           local_inductives context *)
        let is_self_ref = Refset'.mem g ns in
        (* Check if g is a mutual sibling: shares the same MutInd.t KerName
           as any member of ns, but at a different index. Mutual siblings
           need shared_ptr because their types are incomplete (forward-declared). *)
        let is_mutual_sibling =
          (not is_self_ref) &&
          match g with
          | GlobRef.IndRef (kn_g, _) ->
            Refset'.exists (fun r ->
              match r with
              | GlobRef.IndRef (kn_r, _) ->
                MutInd.CanOrd.equal kn_g kn_r
              | _ -> false) ns
          | _ -> false
        in
        let is_local =
          is_self_ref
          || List.exists
               (Environ.QGlobRef.equal Environ.empty_env g)
               !local_inductives
        in
        let is_uniform_self_ref =
          if not is_self_ref then
            true
          else if converted_ts = [] then
            (* Non-parametric inductive: self-reference is trivially uniform.
               The surrounding context may have type vars (e.g. T1 in rect<T1>)
               that are unrelated to the inductive's own parameters — don't
               let those force shared_ptr for a monomorphic self-reference. *)
            true
          else
            List.length converted_ts = List.length tvars
            && List.for_all2
                 (fun ty id ->
                   match ty with
                   | Tvar (_, Some id') -> Id.equal id id'
                   | _ -> false)
                 converted_ts
                 tvars
        in
        if
          (is_self_ref || is_mutual_sibling)
          && not (Table.is_coinductive g)
          && is_uniform_self_ref
        then
          (* Recursive value-type self/mutual references are owned by their
             containing constructor. The pointed-to type may be incomplete at
             field declaration time, so it still needs indirection, but unique
             ownership plus explicit clone is enough. *)
          Tunique_ptr core
        else if is_self_ref || is_mutual_sibling then
          (* Non-uniform recursion and coinductive self-references use
             shared_ptr.  Non-uniform recursion cannot use unique_ptr
             because destructor instantiation diverges.  Coinductive
             recursive fields need shared_ptr because the lazy thunk
             copies the tail reference ([=] capture). *)
          Tshared_ptr core
        else if is_local then
          (* Local non-self inductive: value type, no pointer wrapping *)
          core
        else if not (get_record_fields g == []) then
          (* Record inductive: value type, no pointer wrapping *)
          core
        else
          (* External inductive: value type, namespace-qualified *)
          Tnamespace (g, core)
    | _ -> core )
  | Tvar i | Tvar' i ->
    ( try Tvar (i, Some (List.nth tvars (pred i)))
      with Failure _ -> Tvar (i, None) )
  | Tmeta {contents = Some t} -> convert_ml_type_to_cpp_type env ns tvars t
  | Tmeta {id = i} ->
    (* Unresolved meta - use std::any for type erasure. This happens for
       existential type variables in indexed inductives. *)
    Tany
  (* Tdummy marks erased type/prop/implicit parameters in the ML AST. We convert
     them to Tglob(VarRef "dummy_*") as intermediate markers so that downstream
     filtering (is_cpp_dummy_type / is_erased_type / filter_erased_type_args in
     gen_expr, eta_fun, and gen_decl_for_pp) can detect and drop them. These
     markers should never survive to the C++ output — the filtering pipeline
     removes them from template argument lists and function signatures. *)
  | Tdummy Ktype -> Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
  | Tdummy Kprop -> Tglob (GlobRef.VarRef (Id.of_string "dummy_prop"), [], [])
  | Tdummy (Kimplicit _) ->
    Tglob (GlobRef.VarRef (Id.of_string "dummy_implicit"), [], [])
  | Tstring ->
    Tid_external (Id.of_string_soft "std::string", [])
  | Tunknown -> Tany
  | Taxiom -> Tglob (GlobRef.VarRef (Id.of_string "axiom"), [], [])
(* let _ = print_endline "TODO: TMETA OR TDUMMY OR TUNKNOWN OR TAXIOM" in assert
   false *)

(** Convert ML type arguments to C++ template parameters, applying type
    simplification and handling out-of-scope type variables.

    This function maps a list of ML types to C++ types for use in template
    argument lists. It performs two key transformations:

    1. Type simplification via [type_simpl] to normalize ML types
    2. Conversion to C++ types via [convert_ml_type_to_cpp_type]
    3. Detection and erasure of unbound type variables

    The [tvars] parameter specifies the type variables in scope (as a list of
    typename declarations in the current C++ context). When a [Tvar] appears
    with [None] for its binding and [tvars] is non-empty, this indicates the
    type variable index is out of scope — it references a typename that doesn't
    exist in the current C++ context.

    Out-of-scope type variables are marked as [dummy_type], which triggers
    [filter_erased_type_args] to drop the entire type argument list. This is
    safer than emitting invalid C++ like [template<typename T> ... U] where
    [U] is undefined.

    Example scenario where this occurs:
    - ML function with type scheme [forall A B, A -> B -> option A]
    - Partial application instantiates [A] but leaves [B] polymorphic
    - C++ code generator enters context with only [typename A]
    - Type arg list includes [Tvar 2] for [B]
    - [convert_ml_type_to_cpp_type] returns [Tvar(2, None)] (no binding)
    - We mark it [dummy_type] to trigger erasure

    @param env   Translation environment (unused in current implementation)
    @param tvars Type variables in scope (C++ typename parameters)
    @param tys   ML type arguments to convert
    @return List of C++ types, with out-of-scope Tvars marked as dummy_type *)
and build_template_params env tvars tys =
  (* Template params emitted at expression/function-call sites are public API
     types. Recursive storage wrapping is introduced only when converting
     constructor fields with an explicit storage namespace. *)
  let ns = Refset'.empty in
  List.map
    (fun ty ->
      (* Simplify and convert the ML type to C++ *)
      let t =
        convert_ml_type_to_cpp_type env ns tvars (type_simpl ty)
      in
      (* Check for unbound type variables *)
      match t with
      | Tvar (_, None) when tvars <> [] ->
        (* Type variable has no binding, but we're in a context with typename
           params. This means the Tvar index exceeds the scope of tvars.
           Mark as dummy_type to trigger full erasure via filter_erased_type_args.
           Using the unbound Tvar would generate invalid C++ references. *)
        Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
      | _ ->
        (* Type is either bound, or we're in an untyped context (tvars = []).
           Keep the type as-is. *)
        t )
    tys

(** Generate code for a custom-extracted constructor application.

    Custom-extracted constructors have user-defined C++ syntax (registered via
    [Crane Extract Constant]) that may include type argument placeholders like
    [%t0], [%t1], etc. This function builds the C++ expression by:
    1. Filtering the ML type argument list to keep only type parameters
       (dropping index arguments that don't correspond to C++ template params)
    2. Converting ML types to C++ types via [build_template_params]
    3. Filtering erased types (Tdummy Ktype → dummy_type) to avoid passing
       empty or partial template argument lists to custom syntax
    4. Wrapping in [mk_cppglob] to apply the custom syntax template

    The filtering is critical because custom syntax strings expect concrete
    type arguments for their placeholders. If we pass an empty or erased
    type arg list, the custom syntax renderer in cpp_print.ml will raise
    an anomaly ("Custom syntax: unbound type argument").

    Example:
    - ML: [MLcons(Tglob(option, [Tglob(nat)]), cons_ctor, [5])]
    - Custom syntax: [(Datatypes.option, 0) := "std::optional<%t0>"]
    - After filtering: [std::optional<unsigned int>]
    - Generated C++: [std::make_optional<unsigned int>(5u)]

    Note: This only handles custom constructors. Regular (non-custom) inductives
    follow a different code path via the main [gen_expr] MLcons case.

    @param env Translation environment (contains type context)
    @param ty  ML type of the constructor application (contains type args)
    @param r   Constructor reference (must be custom-extracted)
    @param ts  ML expression arguments (converted to C++ recursively)
    @return C++ expression applying custom syntax with type/value arguments *)

and gen_expr_custom_cons env (ty : ml_type) r ts =
  (* Try to fold binary positive chains inside Z/N constructors to avoid
     unsigned-int overflow.  Zpos(xI(xO(...xH...))) and Zneg(...) chains
     are folded into INT64_C(n) / INT64_C(-n) literals when the parent
     inductive has a numeral format registered via Crane Extract Numeral. *)
  let folded =
    match (r, ts) with
    | GlobRef.ConstructRef ((kn, i), cidx), [inner] ->
      let ind_ref = GlobRef.IndRef (kn, i) in
      ( match Table.get_numeral_info ind_ref with
      | Some info ->
        ( match try_fold_positive inner with
        | Some pos_val ->
          let z_val =
            if cidx = 2 then pos_val
            else if cidx = 3 then Int64.neg pos_val
            else pos_val
          in
          let rendered =
            Str.global_replace
              (Str.regexp_string "%n")
              (Int64.to_string z_val)
              info.Table.num_fmt
          in
          Some (CPPraw rendered)
        | None -> None )
      | None -> None )
    | _ -> None
  in
  match folded with
  | Some e -> e
  | None ->
  (* PROMOTED TYPE VARIABLES in constructor expressions: Use module-level
     aliases (std::any) instead of template-qualified types.

     Inside a template function taking a typeclass parameter, promoted type vars
     normally resolve via [promoted_var_map]:
       [m_carrier] ↦ [typename _tcI0::m_carrier]

     But constructor expressions are NOT in template scope — they're module-level
     static initializers:
       static inline const Functor forward_functor = ...;

     Here, there's no [_tcI0] to qualify. Instead, promoted vars use the
     module-level [using] declaration:
       using Obj = std::any;
       using Hom = std::any;

     So [object_of forward_functor 7] becomes:
       forward_functor->object_of(7u)  // returns std::any
       std::any_cast<unsigned int>(...)  // cast to concrete type

     Setting [in_constructor_expr] makes unresolvable promoted vars (those
     NOT in [promoted_var_map]) fall back to [Tany] = [std::any].

     We do NOT clear [promoted_var_map] here: inside template functions,
     promoted vars must resolve to qualified types (e.g., typename _tcI0::Obj)
     so that constructor type args match the function's declared return type.
     At module level, [promoted_var_map] is already empty, so the
     [in_constructor_expr] fallback handles it naturally. *)
  let saved_in_ctor = tctx.in_constructor_expr in
  tctx.in_constructor_expr <- true;
  (* Convert value arguments to C++ expressions.

     Erased proof/type arguments ([MLdummy]) produce [std::any{}] rather
     than [CPPabort]: the corresponding C++ parameter type is [std::any]
     (all erased types map to [std::any]), and custom constructors like
     [std::make_pair] are evaluated eagerly so a throw would crash at
     runtime.  This mirrors the [gen_ctor_arg] in the [MLcons] case of
     {!gen_expr}. *)
  (* Generate constructor arguments with live move_dead_after so the move
     analysis can fire for single-use variables (nb_occur_match = 1 already
     prevents moving variables that appear more than once across all args). *)
  let gen_ctor_arg e =
    match e with
    | MLdummy _ -> CPPraw "std::any{}"
    | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
      wrap_void_call_as_value (gen_expr env e)
    | _ -> gen_expr env e
  in
  let args = List.rev_map gen_ctor_arg ts in
  (* Helper to wrap expression in function call syntax if it has arguments *)
  let app x =
    match args with
    | [] -> x
    | _ -> CPPfun_call (x, args)
  in
  let result =
    match ty with
    | Miniml.Tglob (n, tys, _) ->
      (* Step 1: Filter out index type args - only keep parameters.

         Inductive types distinguish between parameters (uniform across all
         constructors, e.g., the [A] in [list A]) and indices (may vary,
         e.g., the [n] in [vec A n]). In C++, only parameters become template
         arguments; indices are encoded in types or runtime values.

         We use [get_ind_num_param_vars_opt] to find the parameter count and
         [safe_firstn] to extract them. [safe_firstn] handles cases where the
         type arg list is shorter than expected (e.g., due to Tdummy Ktype
         erasure in make_tyargs). *)
      let tys =
        match n with
        | GlobRef.IndRef (kn, _) ->
          ( match Table.get_ind_num_param_vars_opt kn with
          | Some num_param_vars ->
            (* Take first num_param_vars elements, or fewer if list is short *)
            safe_firstn num_param_vars tys
          | None ->
            (* Not in table - keep all type args *)
            tys )
        | _ ->
          (* Not an inductive ref - keep all type args *)
          tys
      in
      (* Step 2: Convert ML types to C++ types *)
      let temps = build_template_params env [] tys in
      let temps = filter_erased_type_args temps in
      (* Step 2b: Recover type args from the return type when unresolved metas
         caused all type args to be erased.  This happens for nullary custom
         constructors (e.g., None) inside let-bindings: the extraction phase
         uses a fresh meta as the expected type, so the constructor's type
         parameter meta never gets unified with the concrete type.  If the
         enclosing function/constant return type matches the same inductive,
         extract the type args from there. *)
      let temps =
        if temps = [] && tys <> []
           && List.exists (function Miniml.Tmeta {contents = None} -> true | _ -> false) tys
        then
          match tctx.current_cpp_return_type with
          | Some (Minicpp.Tglob (ret_r, ret_tys, _))
            when Names.GlobRef.CanOrd.equal n ret_r
                 && List.length ret_tys = List.length tys ->
            filter_erased_type_args ret_tys
          | Some (Minicpp.Tshared_ptr (Minicpp.Tglob (ret_r, ret_tys, _)))
            when Names.GlobRef.CanOrd.equal n ret_r
                 && List.length ret_tys = List.length tys ->
            filter_erased_type_args ret_tys
          | _ -> temps
        else temps
      in
      app (mk_cppglob r temps)
    | _ ->
      (* Type is not a Tglob - no type args to pass.
         This case is rare for custom constructors, which typically have
         Tglob types. Fall back to bare constructor reference. *)
      app (mk_cppglob r [])
  in
  tctx.in_constructor_expr <- saved_in_ctor;
  (* Collapse identity inline customs (%a0) for constructors, matching
     the same collapse done for function applications at gen_expr. *)
  let result =
    match result with
    | CPPfun_call (CPPglob (_, _, Some ci), [single_arg])
      when ci.ci_inline = Some "%a0" ->
      single_arg
    | _ -> result
  in
  result

(** Try to fold a Peano numeral chain (nested constructors) into an integer *)
and try_fold_numeral info expr =
  match expr with
  | MLcons (_ty, cr, []) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_zero_ctor ->
      Some 0
    | _ -> None )
  | MLcons (_ty, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx = info.Table.num_succ_ctor ->
      Option.map (fun n -> n + 1) (try_fold_numeral info inner)
    | _ -> None )
  | MLmagic inner -> try_fold_numeral info inner
  | _ -> None

(** Try to fold a binary positive chain [xI(xO(...xH...))] into an [int64].
    Returns [Some n] where [n > 0] if the entire chain can be folded, or
    [None] if any node is not a recognized positive constructor.
    Constructors: xI(idx=0) = 2*n+1, xO(idx=1) = 2*n, xH(idx=2) = 1.

    Only folds chains whose parent inductive is registered as [is_custom].
    This is intentionally called from the Z constructor handler, so the
    result can be rendered as [INT64_C(value)] instead of overflowing
    unsigned-int arithmetic. *)
and try_fold_positive expr : int64 option =
  match expr with
  | MLcons (_, GlobRef.ConstructRef (_, 3), []) ->
    (* xH = 1; constructor index 3 (1-based) *)
    Some 1L
  | MLcons (_, GlobRef.ConstructRef (_, 1), [inner]) ->
    (* xI(n) = 2*n + 1; constructor index 1 (1-based) *)
    Option.map (fun n -> Int64.add (Int64.mul 2L n) 1L) (try_fold_positive inner)
  | MLcons (_, GlobRef.ConstructRef (_, 2), [inner]) ->
    (* xO(n) = 2*n; constructor index 2 (1-based) *)
    Option.map (fun n -> Int64.mul 2L n) (try_fold_positive inner)
  | MLmagic inner -> try_fold_positive inner
  | _ -> None

(** Fold a Decimal.uint digit chain into an arbitrary-precision integer.
    Constructors: Nil(idx=1), D0(idx=2, digit 0), ..., D9(idx=11, digit 9).
    Digits are processed outside-in (most significant first).
    Uses [Z.t] from zarith to avoid overflow on large literals. *)
and try_fold_decimal_uint expr acc =
  match expr with
  | MLcons (_, cr, []) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> Some acc
    | _ -> None )
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx >= 2 && cidx <= 11 ->
      let digit = Z.of_int (cidx - 2) in
      try_fold_decimal_uint inner Z.(acc * of_int 10 + digit)
    | _ -> None )
  | MLmagic inner -> try_fold_decimal_uint inner acc
  | _ -> None

(** Fold a Hexadecimal.uint digit chain into an arbitrary-precision integer.
    Constructors: Nil(idx=1), D0(idx=2, digit 0), ..., Df(idx=17, digit 15).
    Uses [Z.t] from zarith to avoid overflow on large literals. *)
and try_fold_hex_uint expr acc =
  match expr with
  | MLcons (_, cr, []) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> Some acc
    | _ -> None )
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, cidx) when cidx >= 2 && cidx <= 17 ->
      let digit = Z.of_int (cidx - 2) in
      try_fold_hex_uint inner Z.(acc * of_int 16 + digit)
    | _ -> None )
  | MLmagic inner -> try_fold_hex_uint inner acc
  | _ -> None

(** Fold a Number.uint (UIntDecimal | UIntHexadecimal) into an
    arbitrary-precision integer.
    Constructors: UIntDecimal(idx=1), UIntHexadecimal(idx=2). *)
and try_fold_num_uint expr =
  match expr with
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> try_fold_decimal_uint inner Z.zero
    | GlobRef.ConstructRef (_, 2) -> try_fold_hex_uint inner Z.zero
    | _ -> None )
  | MLmagic inner -> try_fold_num_uint inner
  | _ -> None

(** Fold a Decimal.signed_int (Pos | Neg) wrapping a Decimal.uint chain.
    Constructors: Pos(idx=1), Neg(idx=2). *)
and try_fold_signed_decimal_int expr =
  match expr with
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> try_fold_decimal_uint inner Z.zero
    | GlobRef.ConstructRef (_, 2) ->
      Option.map Z.neg (try_fold_decimal_uint inner Z.zero)
    | _ -> None )
  | MLmagic inner -> try_fold_signed_decimal_int inner
  | _ -> None

(** Fold a Hexadecimal.signed_int (Pos | Neg) wrapping a Hexadecimal.uint chain.
    Constructors: Pos(idx=1), Neg(idx=2). *)
and try_fold_signed_hex_int expr =
  match expr with
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> try_fold_hex_uint inner Z.zero
    | GlobRef.ConstructRef (_, 2) ->
      Option.map Z.neg (try_fold_hex_uint inner Z.zero)
    | _ -> None )
  | MLmagic inner -> try_fold_signed_hex_int inner
  | _ -> None

(** Fold a Number.signed_int (IntDecimal | IntHexadecimal) into an
    arbitrary-precision integer.
    Constructors: IntDecimal(idx=1), IntHexadecimal(idx=2). *)
and try_fold_num_int expr =
  match expr with
  | MLcons (_, cr, [inner]) ->
    ( match cr with
    | GlobRef.ConstructRef (_, 1) -> try_fold_signed_decimal_int inner
    | GlobRef.ConstructRef (_, 2) -> try_fold_signed_hex_int inner
    | _ -> None )
  | MLmagic inner -> try_fold_num_int inner
  | _ -> None

(** Generate C++ expression from ML AST. Main expression compiler - handles
    lambdas, applications, constructors, pattern matching, etc. Monadic
    non-function globals are wrapped in CPPfun_call by the MLglob case below. *)
and gen_expr env (ml_e : ml_ast) : cpp_expr =
  match ml_e with
  | MLrel i ->
    let var_expr =
      try CPPvar (get_db_name i env)
      with Failure _ -> CPPvar (db_fallback_id i)
    in
    (* Phase 2: move on last use. Emit std::move if: (1) the variable is dead
       after this point, (2) it's an owned variable (not borrowed), and (3) this
       is its only occurrence in the current RHS expression.
       Never move typeclass template parameters (_tcI0, _tcI1, ...) — they
       are type references in the concept paradigm, not owned values. Wrapping
       them in std::move produces invalid C++ like [std::move(_tcI0)::method()]. *)
    let is_tc_param =
      match var_expr with
      | CPPvar id ->
        let s = Id.to_string id in
        String.length s >= 4 && String.sub s 0 4 = "_tcI"
      | _ -> false
    in
    let move_candidate =
      (not is_tc_param)
      && Escape.IntSet.mem i tctx.move_dead_after
      && Escape.IntSet.mem i tctx.move_owned_vars
    in
    if move_candidate then CPPmove var_expr else var_expr
  | MLapp (MLmagic t, args) -> gen_expr env (MLapp (t, args))
  | MLapp (MLglob (r, ret_tys), a1 :: l) when is_ret r ->
    if tctx.itree_mode = Reified then begin
      (* Reified mode: Ret produces ITree<R>::ret(value). Don't strip it. *)
      Table.require_itree_header ();
      let t = Common.last (a1 :: l) in
      match t with
      | MLglob (g, _) when is_ghost g ->
        mk_itree_ret Tvoid []
      | MLcons (_, cr, []) when Table.is_tt_constructor cr ->
        mk_itree_ret Tvoid []
      | _ ->
        let inner = gen_expr env t in
        (* Extract R from the monad's type arguments: itree has template "%t1"
           so the ML type args for Ret are [E, R] where E is typically Tdummy
           and R is the result type. *)
        let tvars = get_current_type_vars () in
        let r_cpp =
          let non_dummy = filter_value_types ret_tys in
          match non_dummy with
          | r_ml :: _ ->
            convert_ml_type_to_cpp_type env Refset'.empty tvars r_ml
          | [] -> Tvoid
        in
        mk_itree_ret r_cpp [inner]
    end
    else begin
      let t = Common.last (a1 :: l) in
      gen_expr env t
    end
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h -> gen_expr env
     (MLapp (a1, a2::[])) *)
  | MLapp (MLglob (r, _), _ :: _ :: _) as a when is_bind r
      && tctx.itree_mode <> Reified ->
    (* Sequential mode: bind in expression context (e.g., nested inside
       another expression). Wrap in IIFE so gen_stmts can sequentialize. *)
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLapp (MLfix _, _) as a ->
    (* Nested fix application in expression context (e.g., S((fix aux ...) es)).
       Wrap in an IIFE, delegating to gen_stmts which handles MLapp(MLfix
       ...). *)
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLapp (MLapp ((MLglob _ as g), inner_args), outer_args) ->
    (* Flatten nested MLapp when inner callee is a global reference. This arises
       from Rocq partial applications like: div_conq_split x f1 f2 l which
       extracts as MLapp(MLapp(MLglob(dcs), [x,f1,f2]), [l]). Flattening to
       MLapp(MLglob(dcs), [x,f1,f2,l]) lets eta_fun see the complete argument
       list and generate a direct call. *)
    eta_fun env g (inner_args @ outer_args)
  | MLapp (MLglob (r, _), [arg]) when Table.is_numeral_converter r ->
    (* Fold Number.uint/signed_int digit chain into a direct integer literal.
       Tries unsigned (of_num_uint) then signed (of_num_int).
       Falls through to eta_fun on failure. *)
    let ind_ref = Option.get (Table.numeral_ind_of_converter r) in
    ( match Table.get_numeral_info ind_ref with
    | Some info ->
      let folded = match try_fold_num_uint arg with
        | Some _ as r -> r
        | None -> try_fold_num_int arg
      in
      ( match folded with
      | Some n ->
        let rendered =
          Str.global_replace
            (Str.regexp_string "%n")
            (Z.to_string n)
            info.Table.num_fmt
        in
        CPPraw rendered
      | None -> eta_fun env (MLglob (r, [])) [arg] )
    | None -> eta_fun env (MLglob (r, [])) [arg] )
  | MLapp (MLcase (typ, scrut, pv), outer_args)
    when Array.length pv = 1
         && not (record_fields_of_type typ == []) ->
    (* Flatten outer args into a single-branch record-projection case body.
       When a typeclass method is partially applied, Rocq extracts it as
       MLcase(instance, [(binds, MLapp(MLrel field, inner_args))]). If this
       MLcase is the callee of an outer MLapp, the inner call only has some
       args while the outer provides the rest — generating a curried C++ call
       like make(a)(b) instead of make(a, b).  Push the outer args into the
       branch body so gen_expr sees the complete argument list. *)
    let (ids, rty, pat, body) = pv.(0) in
    let n_bindings = List.length ids in
    let lifted_outer = List.map (ast_lift n_bindings) outer_args in
    let new_body = match body with
      | MLapp (f, inner_args) -> MLapp (f, inner_args @ lifted_outer)
      | _ -> MLapp (body, lifted_outer)
    in
    gen_expr env (MLcase (typ, scrut, [|(ids, rty, pat, new_body)|]))
  | MLapp (f, args) -> eta_fun env f args
  | MLlam _ as a ->
    let args, a = collect_lams a in
    let lam_params = List.map (fun (x, y) -> (id_of_mlid x, y)) args in
    let args, env = push_vars' lam_params env in
    let saved_env_types = tctx.env_types in
    push_env_types args;
    (* Infer owned/borrowed for each lambda parameter using escape analysis.

       Owned parameters (stored in a data structure or returned) are passed by
       value (shared_ptr<T>), transferring ownership to the callee.  Borrowed
       parameters (only read, not stored/returned) are passed by const ref
       (const shared_ptr<T>&), avoiding a refcount bump on every call.

       The inference is conservative: if a parameter escapes in any code path
       (e.g. captured by a closure, stored in a constructor, or returned), it
       is marked as owned.  See {!Escape.infer_owned_params}. *)
    let n_all_params = List.length lam_params in
    let owned_flags = Escape.infer_owned_params n_all_params a in
    let args_with_owned =
      List.map2 (fun (id, ty) owned -> (id, ty, owned)) args owned_flags
    in
    let filtered_args_with_owned =
      List.filter (fun (_, ty, _) ->
        not (isTdummy ty) && not (ml_type_is_void ty)
        && not (tctx.itree_mode = Reified && ml_type_is_unit ty))
        args_with_owned
    in
    let filtered_args =
      List.map (fun (id, ty, _) -> (id, ty)) filtered_args_with_owned
    in
    let f =
      with_escape_analysis a (fun () ->
        let tvars = get_current_type_vars () in
        let cpp_arg_info =
          List.map
            (fun (id, ty, owned) ->
              let bare_cpp_ty =
                convert_ml_type_to_cpp_type env Refset'.empty tvars ty
              in
              let stored_cpp_ty =
                convert_ml_type_to_cpp_type env tctx.method_self_ns tvars ty
              in
              let body_subst =
                match (bare_cpp_ty, stored_cpp_ty) with
                | Tglob (g1, [], _), Tshared_ptr (Tglob (g2, [], _))
                  when Environ.QGlobRef.equal Environ.empty_env g1 g2 ->
                  Some (id, CPPderef (CPPvar id))
                | _ -> None
              in
              let param_cpp_ty =
                match body_subst with
                | Some _ -> Tref (Tmod (TMconst, stored_cpp_ty))
                | None -> wrap_param_by_ownership ~is_owned:owned bare_cpp_ty
              in
              (param_cpp_ty, Some id, body_subst) )
            filtered_args_with_owned
        in
        let cpp_args =
          List.map (fun (ty, id, _) -> (ty, id)) cpp_arg_info
        in
        (* Generate the body, then check if the body returns a lambda (this
           happens when extract_cons_app generates curried partial constructor
           applications with an MLmagic barrier). If so, convert the returned
           lambda to capture by value to avoid dangling references to the outer
           lambda's parameters. *)
        let body_stmts = gen_stmts env (fun x -> Sreturn (Some x)) a in
        let body_stmts =
          List.fold_left
            (fun stmts (_, _, subst) ->
              match subst with
              | Some (id, expr) -> List.map (local_var_subst_stmt id expr) stmts
              | None -> stmts )
            body_stmts
            cpp_arg_info
        in
        let body_stmts = return_captures_by_value body_stmts in
        CPPlambda (cpp_args, None, body_stmts, true) )
    in
    tctx.env_types <- saved_env_types;
    ( match filtered_args with
    | [] ->
      (* All lambda params are dummy (type abstractions). Skip the lambda
         wrapper and generate the body expression directly. However, when the
         body is a reference to a template function (detectable by having
         Tdummy-typed leading params in its ML type), we must wrap it in a
         generic forwarding lambda — C++ cannot pass overloaded or template
         function names as first-class values. *)
      ( match a with
      | MLglob (r, tys_inner) ->
        let ml_ty =
          match find_type_opt r with
          | Some ty -> ty
          | None -> Tunknown
        in
        let has_dummy_prefix = function
          | Tarr (t, _) when isTdummy t -> true
          | _ -> false
        in
        if has_dummy_prefix ml_ty then
          (* The function is a template that had type-level leading params. We
             need a forwarding lambda because C++ can't pass template function
             names as first-class values.

             To handle non-deducible template type params (like T2 that only
             appears in the return type), we use a C++20 template lambda with
             explicitly typed value parameters. This lets the compiler deduce
             type variables from the argument types, and we compute
             non-deducible tvars via std::invoke_result_t. *)
          let rec collect_non_dummy_types = function
            | Miniml.Tarr (t, rest) when not (isTdummy t) ->
              t :: collect_non_dummy_types rest
            | Miniml.Tarr (_, rest) -> collect_non_dummy_types rest
            | _ -> []
          in
          let non_dummy_param_tys = collect_non_dummy_types ml_ty in
          let n = List.length non_dummy_param_tys in
          let arg_names = List.init n (fun i -> field_param_name i) in
          let fn_name = Common.pp_global_name Term r in
          (* Collect all tvars from the ML type *)
          let all_tvars_set =
            List.fold_left
              collect_tvars_set
              IntSet.empty
              (non_dummy_param_tys @ [ml_ty])
          in
          let all_tvars = IntSet.elements all_tvars_set in
          (* Tvars deducible from non-function value params *)
          let value_param_tys =
            List.filter
              (fun t ->
                match t with
                | Miniml.Tarr _ -> false
                | _ -> true )
              non_dummy_param_tys
          in
          let deducible_set =
            List.fold_left collect_tvars_set IntSet.empty value_param_tys
          in
          let deducible_tvars = IntSet.elements deducible_set in
          let non_deducible_tvars =
            List.filter (fun i -> not (IntSet.mem i deducible_set)) all_tvars
          in
          (* Create tvar names for the template lambda *)
          let tvar_name i = "_T" ^ string_of_int i in
          (* Render an ML type as a C++ value type string using local tvar
             names. Inductives must stay bare values here; recursive ownership
             is represented only inside constructor fields. *)
          let rec render_ml_ty = function
            | Miniml.Tvar i | Miniml.Tvar' i -> tvar_name i
            | Miniml.Tarr (t1, t2) ->
              "std::function<" ^ render_ml_ty t2 ^ "(" ^ render_ml_ty t1 ^ ")>"
            | Miniml.Tglob (g, ts, _) when is_custom g ->
              (* Custom types may use %t0, %t1 placeholders for type args *)
              let custom_str = find_custom g in
              let rendered_ts = Array.of_list (List.map render_ml_ty ts) in
              let n_rendered = Array.length rendered_ts in
              let len = String.length custom_str in
              let buf = Buffer.create len in
              let rec subst i =
                if i >= len then
                  ()
                else if
                  i <= len - 3
                  && custom_str.[i] = '%'
                  && custom_str.[i + 1] = 't'
                  && custom_str.[i + 2] >= '0'
                  && custom_str.[i + 2] <= '9'
                then (
                  let digit_start = i + 2 in
                  let rec find_end j =
                    if j < len && custom_str.[j] >= '0' && custom_str.[j] <= '9'
                    then
                      find_end (j + 1)
                    else
                      j
                  in
                  let digit_end = find_end digit_start in
                  let idx =
                    int_of_string
                      (String.sub
                         custom_str
                         digit_start
                         (digit_end - digit_start) )
                  in
                  if idx < n_rendered then
                    Buffer.add_string buf rendered_ts.(idx)
                  else
                    Buffer.add_string
                      buf
                      (String.sub custom_str i (digit_end - i));
                  subst digit_end )
                else (
                  Buffer.add_char buf custom_str.[i];
                  subst (i + 1) )
              in
              subst 0;
              Buffer.contents buf
            | Miniml.Tdummy _ -> "std::any"
            | Miniml.Tglob (g, ts, _) ->
              let is_ind =
                match g with
                | GlobRef.IndRef _ -> true
                | _ -> false
              in
              let base =
                Common.pp_global_name (if is_ind then Type else Term) g
              in
              if ts = [] then
                base
              else
                base
                ^ "<"
                ^ String.concat ", " (List.map render_ml_ty ts)
                ^ ">"
            | _ -> "auto"
          in
          if non_deducible_tvars <> [] && not (IntSet.is_empty deducible_set)
          then
            (* There are non-deducible tvars — use template lambda with typed
               params. The first param (function type) uses auto&&, value params
               get specific types. *)
            let template_params =
              String.concat
                ", "
                (List.map (fun i -> "typename " ^ tvar_name i) deducible_tvars)
            in
            let params =
              List.mapi
                (fun i ty ->
                  match ty with
                  | Miniml.Tarr _ ->
                    (* Function-typed param: use auto&& *)
                    "auto &&" ^ List.nth arg_names i
                  | _ ->
                    (* Value param: use specific type for tvar deduction *)
                    "const " ^ render_ml_ty ty ^ " &" ^ List.nth arg_names i )
                non_dummy_param_tys
            in
            let params_str = String.concat ", " params in
            let fwd_args =
              String.concat
                ", "
                (List.mapi
                   (fun i ty ->
                     match ty with
                     | Miniml.Tarr _ ->
                       "std::forward<decltype("
                       ^ List.nth arg_names i
                       ^ ")>("
                       ^ List.nth arg_names i
                       ^ ")"
                     | _ -> List.nth arg_names i )
                   non_dummy_param_tys )
            in
            (* Build explicit type args: deducible tvars + non-deducible
               computed via invoke_result_t *)
            let deducible_args = List.map tvar_name deducible_tvars in
            let non_deducible_args =
              List.map
                (fun _i ->
                  (* Compute as invoke_result_t<F&, deducible_tvars&...> where F
                     is the first function param *)
                  let f_param = List.nth arg_names 0 in
                  let deducible_refs =
                    String.concat
                      ", "
                      (List.map (fun j -> tvar_name j ^ " &") deducible_tvars)
                  in
                  "std::invoke_result_t<decltype("
                  ^ f_param
                  ^ ") &, "
                  ^ deducible_refs
                  ^ ">" )
                non_deducible_tvars
            in
            let all_type_args = deducible_args @ non_deducible_args in
            let ty_args_str = "<" ^ String.concat ", " all_type_args ^ ">" in
            CPPraw
              ( "[]<"
              ^ template_params
              ^ ">("
              ^ params_str
              ^ ") -> decltype(auto) { return "
              ^ fn_name
              ^ ty_args_str
              ^ "("
              ^ fwd_args
              ^ "); }" )
          else
            (* No non-deducible tvars or no deducible tvars — simple
               forwarding *)
            let params_str =
              String.concat ", " (List.map (fun s -> "auto &&" ^ s) arg_names)
            in
            let fwd_args =
              String.concat
                ", "
                (List.map
                   (fun s -> "std::forward<decltype(" ^ s ^ ")>(" ^ s ^ ")")
                   arg_names )
            in
            (* Convert inner type args to C++ types, filtering out Tany *)
            let inner_tvars = get_current_type_vars () in
            let tys_cpp =
              List.map
                (convert_ml_type_to_cpp_type env Refset'.empty inner_tvars)
                tys_inner
            in
            let tys_cpp = List.filter (fun t -> t <> Tany) tys_cpp in
            let ty_args_str =
              match tys_cpp with
              | [] -> ""
              | _ ->
                let rec render_ty = function
                  | Tvar (_, Some n) -> Id.to_string n
                  | Tvar (i, None) -> tvar_name i
                  | Tglob (r, [], _) -> Common.pp_global_name Type r
                  | Tglob (r, tys, _) ->
                    Common.pp_global_name Type r
                    ^ "<"
                    ^ String.concat ", " (List.map render_ty tys)
                    ^ ">"
                  | Tshared_ptr ty -> "std::shared_ptr<" ^ render_ty ty ^ ">"
                  | Tunique_ptr ty -> "std::unique_ptr<" ^ render_ty ty ^ ">"
                  | _ -> "auto"
                in
                "<" ^ String.concat ", " (List.map render_ty tys_cpp) ^ ">"
            in
            CPPraw
              ( "[]("
              ^ params_str
              ^ ") -> decltype(auto) { return "
              ^ fn_name
              ^ ty_args_str
              ^ "("
              ^ fwd_args
              ^ "); }" )
        else
          gen_expr env a
      | _ ->
        (* Body is not a template function ref — wrap in void thunk (old
           behavior). gen_expr env a might produce lambdas with [&] capture
           which fail at static scope, so we use the pre-built capture-free
           lambda f.

           Exception: in reified mode, when the lambda had void-typed params
           (from monadic result type erasure), keep the lambda as a function
           object rather than an IIFE. This is needed for itree_bind
           continuations which expect std::function, not the result of
           calling the function. *)
        if tctx.itree_mode = Reified
           && List.exists (fun (_, ty) -> ml_type_is_unit_or_void ty) lam_params then
          f
        else
          CPPfun_call (f, []) )
    | _ -> f )
  | MLglob (x, tys) when is_inline_custom x ->
    let tvars = get_current_type_vars () in
    let ty = find_type x in
    let ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ty in
    ( match ty with
    | Tfun (dom, cod) ->
      eta_fun env (MLglob (x, tys)) [] (* TODO: could be only if contains '%' *)
    | _ -> mk_cppglob x (build_template_params env tvars tys) )
  | MLglob (x, tys) ->
    let tvars = get_current_type_vars () in
    let tys_cpp =
      List.map
        (fun ty ->
          let t =
            convert_ml_type_to_cpp_type env Refset'.empty tvars (type_simpl ty)
          in
          match t with
          | Tvar (_, None) when tvars <> [] ->
            Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
          | _ -> t )
        tys
    in
    (* If any type arg is Tany or a dummy type glob (from erased type/prop
       params), drop ALL explicit type args via filter_erased_type_args and let
       the compiler deduce everything. See filter_erased_type_args for why we
       must drop all args rather than just the erased ones. *)
    let cglob = mk_cppglob x (filter_erased_type_args tys_cpp) in
    (* Monadic non-function definitions (e.g. [base : IO nat]) are generated as
       zero-arg thunks. A bare [MLglob] reference to such a definition must call
       the thunk to obtain its value. CoFixpoint definitions are also zero-arg
       functions and must be called. *)
    let needs_call =
      match find_type_opt x with
      | Some ml_ty when is_monadic_ml_type ml_ty -> true
      | Some _ when Table.is_cofixpoint x -> true
      | Some _ when Table.is_axiom_value x -> true
      | _ -> false
    in
    if needs_call then
      CPPfun_call (cglob, [])
    else
      cglob
  | MLcons (_ty, r, _ts)
    when match r with
         | GlobRef.ConstructRef ((kn, i), _) ->
           Table.is_numeral_inductive (GlobRef.IndRef (kn, i))
         | _ -> false ->
    (* Try to fold Peano numeral chain into an integer literal *)
    let ind_ref =
      match r with
      | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
      | _ -> CErrors.anomaly (Pp.str "try_fold_numeral: expected ConstructRef")
    in
    ( match Table.get_numeral_info ind_ref with
    | Some info ->
      ( match try_fold_numeral info ml_e with
      | Some n ->
        let rendered =
          Str.global_replace
            (Str.regexp_string "%n")
            (string_of_int n)
            info.Table.num_fmt
        in
        CPPraw rendered
      | None ->
        (* Peano folding failed.  Try binary positive folding for
           Z constructors: Zpos(xI(xO(...xH...))) / Zneg(...) chains
           can overflow unsigned int, so fold into INT64_C(n) literals. *)
        let z_folded =
          match (_ts, r) with
          | [inner], GlobRef.ConstructRef (_, cidx) ->
            ( match try_fold_positive inner with
            | Some pos_val ->
              let z_val =
                if cidx = 2 then (* Zpos; ctor 2, 1-based *) pos_val
                else if cidx = 3 then (* Zneg; ctor 3, 1-based *)
                  Int64.neg pos_val
                else 0L
              in
              let rendered =
                Str.global_replace
                  (Str.regexp_string "%n")
                  (Int64.to_string z_val)
                  info.Table.num_fmt
              in
              Some (CPPraw rendered)
            | None -> None )
          | _ -> None
        in
        ( match z_folded with
        | Some e -> e
        | None -> gen_expr_custom_cons env _ty r _ts ) )
    | None -> gen_expr_custom_cons env _ty r _ts )
  | MLcons (ty, r, ts) when is_custom r ->
    gen_expr_custom_cons env ty r ts
  | MLcons (ty, r, ts)
    when ts = []
         &&
         match r with
         | GlobRef.ConstructRef ((kn, _), _) ->
           is_enum_inductive (GlobRef.IndRef (kn, 0))
         | _ -> false ->
    (* Enum constructor: emit bare EnumType::Constructor value *)
    let ctor_name =
      Id.of_string (Common.enum_ctor_name (Common.pp_global_name Type r))
    in
    let ind_ref =
      match r with
      | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
      | _ ->
        CErrors.anomaly
          (Pp.str "gen_expr: enum constructor expected ConstructRef")
    in
    CPPenum_val (ind_ref, ctor_name)
  | MLcons (ty, r, ts) ->
    (* Setting [in_constructor_expr] makes unresolvable promoted vars (those
       NOT in [promoted_var_map]) fall back to [Tany] = [std::any].

       For non-record constructors (fds = []), we keep [promoted_var_map] so
       that template type annotations (e.g., SigT<..., Path<typename
       _tcI0::Obj>>) match the function's declared return type.

       For record constructors (fds != []), we clear [promoted_var_map]
       because record structs use erased types (std::any) for promoted fields,
       so lambda parameters assigned to record fields must also use std::any. *)
    let saved_promoted_cons = tctx.promoted_var_map in
    let saved_in_ctor_cons = tctx.in_constructor_expr in
    tctx.in_constructor_expr <- true;
    let fds = record_fields_of_type ty in
    let cons_result = match fds with
    | [] ->
      (* Propagate resolved types to nested list constructors before code
         generation. For List<nat> constructors like cons(1, cons(2, nil)), this
         ensures the nested nil gets List<nat> type instead of
         List<std::any>. *)
      let ts_updated =
        match ty with
        | Tglob (n, tys_orig, schema_opt) ->
          (* Only run type propagation for list constructors *)
          let is_list =
            try String.equal (Common.pp_global_name Type n) "list"
            with _ -> false
          in
          if not is_list then
            ts
          else (* Filter out index type args - only keep parameters *)
            let tys_filt =
              match n with
              | GlobRef.IndRef (kn, _) ->
                ( match Table.get_ind_num_param_vars_opt kn with
                | Some num_param_vars -> safe_firstn num_param_vars tys_orig
                | None -> tys_orig )
              | _ -> tys_orig
            in
            (* Resolve Tunknown from element types *)
            let has_unknown =
              List.exists
                (fun (t : ml_type) ->
                  match t with
                  | Tunknown -> true
                  | _ -> false )
                tys_filt
            in
            if
              has_unknown
              &&
              match ts with
              | [] -> false
              | _ -> true
            then
              let tys_resolved =
                List.map
                  (fun (t : ml_type) ->
                    match t with
                    | Tunknown ->
                      let first_elem =
                        List.find_opt
                          (fun a ->
                            match a with
                            | MLdummy _ -> false
                            | _ -> true )
                          ts
                      in
                      ( match first_elem with
                      | Some (MLmagic (MLcons (elem_ty, _, _))) -> elem_ty
                      | Some (MLcons (elem_ty, _, _)) -> elem_ty
                      | _ -> t )
                    | _ -> t )
                  tys_filt
              in
              (* Propagate resolved type to nested constructors *)
              let resolved_ty = Miniml.Tglob (n, tys_resolved, schema_opt) in
              let rec update_nested_ty ast =
                match ast with
                | MLcons (arg_typ, arg_c, arg_ts) ->
                  ( match arg_typ with
                  | Miniml.Tglob (arg_ref, arg_tys, _)
                    when GlobRef.CanOrd.equal arg_ref n
                         && List.exists
                              (fun t ->
                                match t with
                                | Miniml.Tunknown -> true
                                | _ -> false )
                              arg_tys ->
                    MLcons (resolved_ty, arg_c, List.map update_nested_ty arg_ts)
                  | _ ->
                    MLcons (arg_typ, arg_c, List.map update_nested_ty arg_ts) )
                | MLmagic inner -> MLmagic (update_nested_ty inner)
                | other -> other
              in
              List.map update_nested_ty ts
            else
              ts
        | _ -> ts
      in
      (* Generate: Type<temps>::ctor::Constructor_(args) *)
      let gen_ctor_call args =
        match ty with
        | Tglob (n, tys, _) ->
          (* Filter out index type args - only keep parameters *)
          let tys =
            match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys
              | None -> tys )
            | _ -> tys
          in
          (* Resolve Tunknown type args from constructor element types. For
             cons(elem, rest), elem's type provides the list's type param. *)
          let has_unknown =
            List.exists
              (fun (t : ml_type) ->
                match t with
                | Tunknown -> true
                | _ -> false )
              tys
          in
          let tys =
            if
              has_unknown
              &&
              match ts_updated with
              | [] -> false
              | _ -> true
            then
              List.map
                (fun (t : ml_type) ->
                  match t with
                  | Tunknown ->
                    (* Infer from first non-MLmagic/MLdummy constructor arg *)
                    let first_elem =
                      List.find_opt
                        (fun a ->
                          match a with
                          | MLdummy _ -> false
                          | _ -> true )
                        ts_updated
                    in
                    ( match first_elem with
                    | Some (MLmagic (MLcons (elem_ty, _, _))) -> elem_ty
                    | Some (MLcons (elem_ty, _, _)) -> elem_ty
                    | _ -> t )
                  | _ -> t )
                tys
            else
              tys
          in
          let tvars = get_current_type_vars () in
          let temps = build_template_params env tvars tys in
          (* In dependent types, if a constructor arg at position i is
             [MLdummy Ktype] (a type-valued argument — e.g. [x : A] where
             [A : Type]), any template param at a later position j > i must
             also be erased to [std::any].
             Rationale: later params often have types that are functions of
             the erased type variable (e.g. [P x] for [sigT A P]).  When A
             is erased, [P x] is equally abstract and the concrete type
             inferred from the value argument (e.g. [bool] from [true : bool])
             would produce an incompatible template instantiation
             ([SigT<std::any, Bool0>] vs. the declared [SigT<std::any, std::any>]). *)
          let temps =
            let rec first_ktype_dummy i = function
              | [] -> max_int
              | (MLdummy Ktype | MLmagic (MLdummy Ktype)) :: _ -> i
              | _ :: rest -> first_ktype_dummy (i + 1) rest
            in
            let cutoff = first_ktype_dummy 0 ts_updated in
            List.mapi (fun i t -> if i > cutoff then Tany else t) temps
          in
          let ctor_struct = ctor_struct_name_of_ref r in
          let ind_type_name = Common.pp_global_name Type n in
          let fname =
            factory_name_of_ctor ~type_name:ind_type_name ctor_struct
          in
          (* Build: Type<temps>::factory(args) *)
          let type_expr = mk_cppglob n temps in
          CPPfun_call (CPPqualified (type_expr, Id.of_string fname), args)
        | _ ->
          (* Fallback for non-Tglob types *)
          let ctor_struct = ctor_struct_name_of_ref r in
          let fname = factory_name_of_ctor ctor_struct in
          CPPfun_call (CPPqualified (mk_cppglob r [], Id.of_string fname), args)
      in
      (* [CPPfun_call] stores args reversed; [List.rev_map] compensates.
         Erased proof/type args ([MLdummy]) produce [std::any{}] — the
         corresponding C++ parameter type is [std::any] and [CPPabort]
         would throw at runtime.  The same pattern is used in
         {!gen_expr_custom_cons} for inline-extracted constructors
         (e.g., [std::make_pair]). *)
      (* Generate constructor arguments with live move_dead_after so the move
         analysis from gen_tail_expr flows through.  Safety note: gen_tail_expr
         only marks variables that occur exactly once in the entire tail
         expression (nb_occur_match = 1), so a variable appearing in multiple
         constructor args is NOT in move_dead_after and cannot be moved twice. *)
      let gen_ctor_arg e =
        match e with
        | MLdummy _ -> CPPraw "std::any{}"
        | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
          wrap_void_call_as_value (gen_expr env e)
        | _ -> gen_expr env e
      in
      (* When a constructor's field type is a type variable (Tvar i) that
         resolves to an owning pointer type (because T is in method_self_ns),
         the generated arg expression is a bare T value.  Wrap it so the
         field's stored type matches. *)
      let ctor_temps = match ty with
        | Tglob (n, tys_orig, _) ->
          let tys_filt = match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys_orig
              | None -> tys_orig )
            | _ -> tys_orig
          in
          let tvars = get_current_type_vars () in
          build_template_params env tvars tys_filt
        | _ -> []
      in
      let field_types = match Table.get_ctor_ip_types_opt r with
        | Some ft -> ft | None -> [] in
      let wrap_if_needed_for_field ft expr =
        match ft with
        | Miniml.Tvar i | Miniml.Tvar' i ->
          ( try match List.nth ctor_temps (i - 1) with
            | Tshared_ptr inner ->
              let inner_g = match inner with
                | Tglob (g, _, _) -> Some g | _ -> None in
              ( match inner_g with
              | Some g when Refset'.mem g tctx.method_self_ns ->
                CPPfun_call (CPPmk_shared inner, [expr])
              | _ -> expr )
            | Tunique_ptr inner ->
              let inner_g = match inner with
                | Tglob (g, _, _) -> Some g | _ -> None in
              ( match inner_g with
              | Some g when Refset'.mem g tctx.method_self_ns ->
                CPPfun_call (CPPmk_unique inner, [expr])
              | _ -> expr )
            | _ -> expr
            with Failure _ | Invalid_argument _ -> expr )
        | _ -> expr
      in
      let gen_and_wrap i e =
        let expr = gen_ctor_arg e in
        let ft_opt =
          try Some (List.nth field_types i)
          with Failure _ | Invalid_argument _ -> None
        in
        match ft_opt with
        | Some ft -> wrap_if_needed_for_field ft expr
        | None -> expr
      in
      gen_ctor_call (List.rev (List.mapi gen_and_wrap ts_updated))
    | _ ->
      (* Records: clear [promoted_var_map] because record structs use erased
         types (std::any) for promoted fields.  Lambda parameters assigned to
         record fields must use std::any to match the field types. *)
      tctx.promoted_var_map <- [];
      let nstempmod args =
        match ty with
        | Tglob (n, tys, _) ->
          (* Filter out index type args - only keep parameters *)
          let tys =
            match n with
            | GlobRef.IndRef (kn, _) ->
              ( match Table.get_ind_num_param_vars_opt kn with
              | Some num_param_vars -> safe_firstn num_param_vars tys
              | None -> tys )
            | _ -> tys
          in
          let temps = build_template_params env [] tys in
          if Table.is_coinductive n then
            CPPfun_call
              (CPPmk_shared (Tglob (n, temps, [])), [CPPstruct (n, temps, args)])
          else
            (* Value-type records: direct construction, no make_shared *)
            CPPstruct (n, temps, args)
        | _ ->
          CErrors.anomaly
            (Pp.str
               "gen_expr: non-record MLcons with matching type expected Tglob" )
      in
      (* Defense-in-depth: same safeguard as for non-record constructors above *)
      let saved_dead = tctx.move_dead_after in
      tctx.move_dead_after <- Escape.IntSet.empty;
      let record_arg_exprs =
        let base_args =
          List.map
            (fun e ->
              match e with
              | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
                wrap_void_call_as_value (gen_expr env e)
              | _ -> gen_expr env e)
            ts
        in
        match ty with
        | Tglob (n, _, _) ->
          let field_types =
            match Table.get_ctor_ip_types_opt r with
            | Some ft -> ft
            | None -> []
          in
          let tvars = get_current_type_vars () in
          List.mapi
            (fun i expr ->
              match List.nth_opt field_types i with
              | Some ft ->
                let storage_ty =
                  convert_ml_type_to_cpp_type
                    env
                    (Refset'.add n Refset'.empty)
                    tvars
                    ft
                in
                let api_ty =
                  convert_ml_type_to_cpp_type env Refset'.empty tvars ft
                in
                wrap_storage_expr ~storage_ty ~api_ty expr
              | None -> expr)
            base_args
        | _ -> base_args
      in
      let result = nstempmod record_arg_exprs in
      tctx.move_dead_after <- saved_dead;
      result
    in
    tctx.promoted_var_map <- saved_promoted_cons;
    tctx.in_constructor_expr <- saved_in_ctor_cons;
    cons_result
  | MLcase (typ, t, pv) when is_custom_match pv ->
    let tvars = get_current_type_vars () in
    let iife_ret =
      let branch_rty =
        match Array.to_list pv with
        | (_, rty, _, _) :: _ -> rty
        | [] -> typ
      in
      let r = convert_ml_type_to_cpp_type env Refset'.empty tvars branch_rty in
      if is_cpp_unit_type r
         || ml_type_is_unit (ml_result_type branch_rty)
      then Tvoid else r
    in
    let saved_ret = tctx.current_cpp_return_type in
    if iife_ret = Tvoid then
      tctx.current_cpp_return_type <- Some Tvoid;
    let stmts = gen_custom_cpp_case env (fun x -> Sreturn (Some x)) typ t pv in
    tctx.current_cpp_return_type <- saved_ret;
    CPPfun_call (CPPlambda ([], Some iife_ret, stmts, false), [])
  | MLcase (typ, t, pv)
    when (not (record_fields_of_type typ == [])) && Array.length pv == 1 ->
    let ids, r, pat, body = pv.(0) in
    let n = List.length ids in
    let is_typeclass = Table.is_typeclass_type typ in
    (* Build lists that correctly account for erased fields.
       record_fields_of_type includes None entries for erased fields; ids only
       contains non-erased bindings. So MLrel i refers to the i-th non-erased
       field. We filter out None entries for correct indexing. *)
    let all_fields = record_fields_of_type typ in
    let non_erased_fields = List.filter_map Fun.id all_fields in
    let all_field_types =
      match typ with
      | Tglob (r, _, _) -> Table.record_field_types r
      | _ -> []
    in
    let non_erased_field_types =
      filter_value_types all_field_types
    in
    let record_ref_opt =
      match typ with Tglob (r, _, _) -> Some r | _ -> None
    in
    let wrap_record_field_to_api idx access =
      match (record_ref_opt, List.nth_opt non_erased_field_types idx) with
      | Some record_ref, Some ml_ty ->
        let tvars = get_current_type_vars () in
        let storage_ty =
          convert_ml_type_to_cpp_type
            env
            (Refset'.add record_ref Refset'.empty)
            tvars
            ml_ty
        in
        let api_ty =
          convert_ml_type_to_cpp_type env Refset'.empty tvars ml_ty
        in
        wrap_api_expr ~storage_ty ~api_ty access
      | _ -> access
    in
    (* For type classes, use qualified access (::) instead of arrow (->) since
       type class instances are template type parameters, not runtime values *)
    let make_field_access base_expr fld =
      if is_typeclass then
        let fld_name = Id.of_string (Common.pp_global_name Term fld) in
        CPPqualified (base_expr, fld_name)
      else
        CPPget' (base_expr, fld)
    in
    (* Strip MLmagic wrappers from the body — promoted dependent records may
       wrap field references in MLmagic due to Tvar/Tglob mismatches *)
    let body' =
      match body with
      | MLmagic b -> b
      | b -> b
    in
    ( match body' with
    | MLrel i when i <= n ->
      let fld =
        try Some (List.nth non_erased_fields (n - i)) with _ -> None
      in
      ( match fld with
      | Some fld ->
        let access = make_field_access (gen_expr env t) fld in
        let access = wrap_record_field_to_api (n - i) access in
        if is_typeclass then
          (* For typeclasses, non-function value fields (like m_id : carrier)
             are generated as nullary static methods, so we need () to call
             them *)
          let fld_ty =
            try List.nth non_erased_field_types (n - i)
            with _ -> Miniml.Tunknown
          in
          let is_value_field =
            match fld_ty with
            | Miniml.Tarr _ -> false
            | _ -> true
          in
          if is_value_field then
            CPPfun_call (access, [])
          else
            access
        else
          access
      | _ ->
        CErrors.anomaly (Pp.str "record field index out of bounds") )
    | MLapp ((MLrel i | MLmagic (MLrel i)), args) when i <= n ->
      let fld =
        try Some (List.nth non_erased_fields (n - i)) with _ -> None
      in
      let _, env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      ( match fld with
      (* [CPPfun_call] expects args in reverse order; [List.rev_map] both
         converts and reverses.  Filter [MLdummy] args — these are erased type
         parameters (e.g. [A : Type] in [f : forall A, A -> A]) with no C++
         runtime representation.  When the field's codomain erases to [std::any]
         (see [ml_codomain_erases_to_any]), wrap the result with
         [std::any_cast<T>] to recover the caller's concrete return type. *)
      | Some fld ->
        let value_args =
          List.filter (fun a -> match a with MLdummy _ -> false | _ -> true) args
        in
        let call =
          CPPfun_call
            ( make_field_access (gen_expr env t) fld,
              List.rev_map (gen_expr env') value_args )
        in
        let fld_ty_opt =
          try Some (List.nth non_erased_field_types (n - i)) with _ -> None
        in
        let n_value_args = List.length value_args in
        let erased_cod =
          match fld_ty_opt with
          | Some ft -> ml_codomain_erases_to_any n_value_args ft
          | None -> false
        in
        ( match (erased_cod, tctx.current_cpp_return_type) with
        | (true, Some ty) when ty <> Tany && not (is_erased_type ty) && ty <> Tvoid ->
          CPPany_cast (ty, call)
        | _ -> call )
      | _ -> CErrors.anomaly (Pp.str "record field index out of bounds") )
    | _ ->
      (* Destructure record fields into local variables, then evaluate the body
         in an IIFE. push_vars' may rename variables to avoid shadowing
         identifiers already in scope — e.g. when a record has a field
         [rn_value] and the enclosing struct also has an accessor method
         [rn_value], push_vars' renames the local to [rn_value0].

         We must use the renamed ids from push_vars' for the assignment
         declarations so that they are consistent with env' (which the body is
         generated under). Otherwise the declarations would use the original
         names while the body references the renamed ones. *)
      let renamed_ids, env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      (* renamed_ids is in reversed order (from List.rev_map above). Reverse it
         back so it aligns with ids (constructor / field order). *)
      let renamed_ids_fwd = List.rev renamed_ids in
      let asgns =
        List.mapi
          (fun i ((renamed_name, _), (_, ty)) ->
            let fld =
              try Some (List.nth non_erased_fields i) with _ -> None
            in
            let e =
              match fld with
              | Some fld -> make_field_access (gen_expr env t) fld
              | _ -> CErrors.anomaly (Pp.str "record field index out of bounds")
            in
            let e =
              match typ with
              | Tglob (record_ref, _, _) ->
                let storage_ty =
                  convert_ml_type_to_cpp_type
                    env
                    (Refset'.add record_ref Refset'.empty)
                    []
                    ty
                in
                let api_ty =
                  convert_ml_type_to_cpp_type env Refset'.empty [] ty
                in
                wrap_api_expr ~storage_ty ~api_ty e
              | _ -> e
            in
            Sasgn
              ( renamed_name,
                Some (convert_ml_type_to_cpp_type env Refset'.empty [] ty),
                e ) )
          (List.combine renamed_ids_fwd ids)
      in
      CPPfun_call
        ( CPPlambda
            ( [],
              None,
              asgns @ gen_stmts env' (fun x -> Sreturn (Some x)) body,
              false ),
          [] ) )
    (* Known limitation: simultaneous pattern matching on record fields is not
       supported — each field is destructured individually. *)
  | MLcase (typ, t, pv) when lang () == Cpp -> gen_cpp_case typ t env pv
  | MLletin (_, ty, _, _) as a ->
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLfix _ as a ->
    (* Bare fixpoint in expression context — wrap in IIFE, delegate to
       gen_stmts. *)
    with_escape_analysis a (fun () ->
      CPPfun_call
        ( CPPlambda
            ([], None, gen_stmts env (fun x -> Sreturn (Some x)) a, false),
          [] ) )
  | MLstring s -> CPPstring s
  | MLuint x -> CPPuint x
  | MLfloat f -> CPPfloat f
  | MLparray (elems, def) ->
    let elems = Array.map (gen_expr env) elems in
    let def = gen_expr env def in
    CPPparray (elems, def)
  | MLmagic t -> gen_expr env t
  | MLdummy _ ->
    (* Erased proof or type argument.  [CPPabort] is safe here because this
       case only fires in dead code positions (absurd match branches).
       Evaluated positions — constructor args and custom-constructor args —
       are handled before reaching this point: see [gen_ctor_arg] in the
       [MLcons] case and in {!gen_expr_custom_cons}, which produce
       [std::any{}] instead.  The reuse optimization in {!gen_cpp_case}
       skips [MLdummy] fields entirely. *)
    CPPabort "unreachable"
  | MLexn msg ->
    (* Unreachable/absurd case - e.g., match on empty type *)
    CPPabort msg
  | MLaxiom s -> CPPabort ("unrealized axiom: " ^ s)
  | _ -> raise TODO

(** Handle eta expansion, curried function application, and promoted type arg
    resolution. Recovers erased template type args at call sites where C++ can't
    deduce them from lambda arguments, using the enclosing function's return
    type.

    In the normal (exact-application) case, also detects calls that return
    [std::any] because the callee is higher-rank polymorphic — either a record
    field (e.g. [apply : forall A, A -> A] stored as
    [std::function<std::any(std::any)>]) or an [MLrel] callback with a
    [Tdummy]-guarded [Tvar] codomain.  When such a call is made in a context
    where the enclosing function's return type is a concrete C++ type [T], the
    result is wrapped with [std::any_cast<T>].  See [ml_codomain_erases_to_any]. *)
and eta_fun env f args =
  let rec get_eta_args dom args =
    match (dom, args) with
    | _ :: dom, _ :: args -> get_eta_args dom args
    | _, _ -> dom
  in
  (* Check if an ML arg is a type class instance (a reference to a struct that
     implements a type class) *)
  let is_typeclass_instance_arg ml_arg =
    match ml_arg with
    | MLglob (r, _) ->
      ( match find_type_opt r with
      | Some arg_ty -> Table.is_typeclass_type arg_ty
      | None -> false )
      || ref_returns_skipped r
    | MLrel i ->
      (* Check if the referenced parameter is a type class instance *)
      ( try
          let db, _ = env in
          let _name = List.nth db (pred i) in
          (* Look up the type of this de Bruijn variable in the env's type context *)
          (* Check if the name matches our typeclass instance naming: _tcI0, _tcI1, etc. *)
          (* This is a heuristic - ideally we'd track types in the env *)
          let name_str = Id.to_string _name in
          String.length name_str >= 5 && String.sub name_str 0 4 = "_tcI"
        with _ -> false )
    | MLapp (MLglob (r, _), _) ->
      (* Parameterized instance application, e.g. numList A H. Check if r's
         return type (after stripping Tarr) is a typeclass type, or if it
         returns a skipped type (e.g. ReSum instances where the Class is a
         ConstRef not recognized by is_typeclass). *)
      ref_returns_typeclass r || ref_returns_skipped r
    | MLcase (case_ty, _scrutinee, branches) when Array.length branches = 1 ->
      (* Single-branch case = record field projection.  If the projected
         field's type is itself a typeclass, this is a typeclass instance
         arg — e.g., [base_category(PS)] projects a [PreCategory]-typed
         field from a [PreStableCategory] record.
         Look up the record's field types from the case type rather than
         relying on branch binding types (which may be Tunknown). *)
      let (binds, _, _, br_body) = branches.(0) in
      ( match br_body with
      | MLrel j when j >= 1 && j <= List.length binds ->
        let idx = List.length binds - j in
        (* Try to get the field type from the record definition *)
        let field_is_tc =
          match case_ty with
          | Tglob (r, _, _) when Table.is_typeclass r ->
            let field_types = Table.record_field_types r in
            let non_dummy =
              filter_value_types field_types
            in
            ( try
                let fty = List.nth non_dummy idx in
                Table.is_typeclass_type fty
              with _ -> false )
          | _ -> false
        in
        field_is_tc
      | _ -> false )
    | _ -> false
  in
  (* Save and clear the single-use closure flag so that nested eta_fun calls
     (from processing args) do not inherit it. The saved value is used when
     this eta_fun constructs a partial-application lambda. *)
  let eta_keep_moves = tctx.eta_keep_moves in
  tctx.eta_keep_moves <- false;
  match f with
  | MLglob (id, tys) ->
    (* When the call has more args than the function's ML value-domain, the
       excess args are curried applications to the result. This is common with
       Rocq's Function vernacular _correct proof terms, where the extraction
       produces e.g. div2_rect f f0 f1 n _res __ but div2_rect only has 4
       value-domain params (f, f0, f1, n). The trailing _res and __ are applied
       to the result via currying.

       Split into: - primary_args: first n_value_dom args (passed to the
       function) - excess_args: remaining non-dummy args (curried onto the
       result) Only activates when n_args > n_value_dom; otherwise unchanged. *)
    let args, excess_args =
      let is_value_arg = function
        | MLdummy _ -> false
        | _ -> true
      in
      let is_value_dom t =
        match resolve_tmeta t with
        | Miniml.Tdummy _ -> false
        | _ -> true
      in
      let rec collect_tarr_dom acc = function
        | Miniml.Tarr (t1, t2) -> collect_tarr_dom (resolve_tmeta t1 :: acc) t2
        | _ -> List.rev acc
      in
      match find_type_opt id with
      | Some ml_ty ->
        let all_dom = collect_tarr_dom [] ml_ty in
        (* Count value-domain entries by filtering out ALL [Tdummy] positions
           (both [Ktype] for erased type params and [Kprop] for erased proofs).
           Symmetrically, filter the arg list to exclude [MLdummy] entries.
           Comparing these two filtered counts avoids false excess detection
           when erased params appear in [args] as [MLdummy] instead of (or in
           addition to) being carried in [tys]. *)
        let n_value_dom = List.length (List.filter is_value_dom all_dom) in
        let value_args = List.filter is_value_arg args in
        let n_value_args = List.length value_args in
        if n_value_args > n_value_dom then
          let primary =
            List.filteri (fun i _ -> i < n_value_dom) value_args
          in
          let excess =
            List.filteri (fun i _ -> i >= n_value_dom) value_args
          in
          (primary, excess)
        else
          (value_args, [])
      | None -> (List.filter is_value_arg args, [])
    in
    (* Partition args into type class instances and regular args *)
    let typeclass_ml_args, regular_ml_args =
      List.partition is_typeclass_instance_arg args
    in
    (* Reverse typeclass args to match template param order from gen_dfun:
       gen_dfun iterates collect_lams output (reversed from source) so the first
       typeclass in that order becomes 'i'. Call sites have args in source
       order, so we reverse to match. *)
    let typeclass_ml_args = List.rev typeclass_ml_args in
    (* Convert type class instance args to template type arguments *)
    let rec ml_arg_to_template_type ml_arg =
      match ml_arg with
      | MLglob (r, ts) ->
        if ref_returns_skipped r then
          (* Skipped infrastructure (e.g. ReSum_id) — erase to void *)
          Tvoid
        else
          (* Use the instance struct as a type - convert to Tglob *)
          Tglob (r, build_template_params env [] ts, [])
      | MLrel i ->
        (* The instance is a lambda parameter - look up its name in the env and
           create a Tvar reference to the template parameter *)
        let db, _ = env in
        let name = List.nth db (pred i) in
        Tvar (0, Some name)
      | MLapp (MLglob (r, _), _) when ref_returns_skipped r ->
        (* Skipped infrastructure (e.g. ReSum_inl applied to args) — the inner
           args are complex and cannot be converted to C++ template types.
           Erase to void since these type args are never referenced. *)
        Tvoid
      | MLapp (MLglob (r, ts), inner_args) ->
        (* Parameterized instance application, e.g. numList A H. Convert to
           Tglob(r, template_args, []) where template_args are built from the
           inner args. *)
        let template_args =
          List.filter_map
            (fun arg ->
              match arg with
              | MLdummy _ -> None (* Erased type param — skip *)
              | _ -> Some (ml_arg_to_template_type arg) )
            inner_args
        in
        Tglob (r, build_template_params env [] ts @ template_args, [])
      | MLcase (_, scrutinee, branches)
        when Array.length branches = 1 ->
        (* Record field projection — e.g., [base_category(PS)].
           Resolve to [Tqualified(scrutinee_type, field_name)]. *)
        let (binds, _, _, br_body) = branches.(0) in
        let base_ty = ml_arg_to_template_type scrutinee in
        ( match br_body with
        | MLrel j when j >= 1 && j <= List.length binds ->
          let idx = List.length binds - j in
          let (field_id, _) = List.nth binds idx in
          ( match field_id with
          | Id name | Tmp name -> Tqualified (base_ty, name)
          | Dummy -> Tany )
        | _ -> Tany )
      | MLapp (f, args) ->
        (* Parameterized instance application with non-glob head.
           Resolve head, then add arg types. *)
        let head_ty = ml_arg_to_template_type f in
        let arg_tys =
          List.filter_map
            (fun arg ->
              match arg with
              | MLdummy _ -> None
              | _ -> ( try Some (ml_arg_to_template_type arg)
                        with _ -> None ) )
            args
        in
        ( match head_ty with
        | Tglob (r, existing, es) ->
          Tglob (r, existing @ arg_tys, es)
        | _ -> head_ty )
      | MLdummy _ -> Tany (* Should not happen at top level, but be safe *)
      | _ ->
        CErrors.anomaly
          (Pp.str
             "ml_arg_to_template_type: unexpected ML term after \
              is_typeclass_instance_arg filter" )
    in
    let typeclass_type_args =
      List.map ml_arg_to_template_type typeclass_ml_args
    in
    (* Filter out MLdummy entries from regular args — these are erased proof
       arguments that would generate CPPabort "unreachable" expressions and
       inflate the argument count for eta expansion. *)
    let regular_ml_args =
      List.filter
        (fun x ->
          match x with
          | MLdummy _ -> false
          | _ -> true )
        regular_ml_args
    in
    (* Compute the function's ML type after type arg substitution, to detect
       arguments that return std::any (from erased record fields like
       Functor::object_of) but where the parameter expects a concrete type
       (e.g., unsigned int after resolving a promoted type var). *)
    let fn_ml_ty = find_type id in
    let fn_ml_ty_subst = try type_subst_list tys fn_ml_ty with _ -> fn_ml_ty in
    let fn_param_ml_tys =
      let rec collect = function
        | Miniml.Tarr (t, rest) ->
          (match resolve_tmeta t with Miniml.Tdummy _ -> collect rest | t -> t :: collect rest)
        | _ -> []
      in
      collect fn_ml_ty_subst
    in
    (* Non-substituted parameter types: used to detect whether a callback's
       codomain is a type variable (needs adapter wrapping) vs concrete unit
       (C++ definition already uses void in MapsTo constraint). *)
    let fn_param_ml_tys_orig =
      let rec collect = function
        | Miniml.Tarr (t, rest) ->
          (match resolve_tmeta t with Miniml.Tdummy _ -> collect rest | t -> t :: collect rest)
        | _ -> []
      in
      collect fn_ml_ty
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
      if tys <> [] || excess_args = [] then
        None
      else
        let resolve_tmeta_local = function
          | Miniml.Tmeta {contents = Some t} -> t
          | t -> t
        in
        match tctx.current_cpp_return_type with
        | None -> None
        | Some ret_ty ->
          match find_type_opt id with
          | None -> None
          | Some ml_ty_orig ->
            let ret = resolve_tmeta_local (ml_return_type ml_ty_orig) in
            ( match ret with
            | Miniml.Tvar _ | Miniml.Tvar' _ ->
              (* Compute excess arg C++ types from de Bruijn lookup. *)
              let excess_cpp_tys =
                List.filter_map
                  (fun ml_arg ->
                    match ml_arg with
                    | MLrel i ->
                      ( match get_param_type_by_index i with
                      | Some ml_ty ->
                        Some (convert_ml_type_to_cpp_type
                                env Refset'.empty tvars ml_ty)
                      | None -> None )
                    | _ -> None )
                  excess_args
              in
              if List.length excess_cpp_tys = List.length excess_args then
                Some (Tfun (excess_cpp_tys, ret_ty))
              else
                None
            | _ -> None )
    in
    let args = List.mapi (fun i ml_arg ->
      (* {b Lambda arity limiting.}  When a lambda argument has more binders
         than the callee's parameter type has top-level arrows, the extra
         binders come from the return type being a function (instantiated
         from a type variable).  For example, [fold_right]'s callback type
         is [B -> A -> A]; when [A = nat -> nat], the lambda
         [fun t acc => fun x => body] has 3 binders but the parameter has
         only 2 arrows.  Flattening all 3 into a single C++ lambda produces
         a 3-arg function, which doesn't match the 2-arg [MapsTo] concept.

         Fix: insert an [MLmagic] barrier after the expected number of
         binders so that [collect_lams] in [gen_expr] stops there.  The
         inner binders become a returned inner lambda.  We use the
         {i non-substituted} parameter type to count arrows, because type
         variable substitution would inflate the count (e.g. [Tvar A]
         becoming [Tarr(nat, nat)] adds a spurious arrow).

         Additionally, annotate the outer lambda with an explicit return
         type derived from the {i substituted} parameter type's codomain.
         Without this, the deduced return type is the inner lambda's
         unique closure type, and [is_invocable_r_v<std::function<...>,
         closure_type>] may evaluate to [false] in concept checking
         (C++ lambda-to-[std::function] conversion is not recognized
         during SFINAE in some implementations). *)
      let ml_arg, split_ret_ty =
        match ml_arg with
        | MLlam _ ->
          ( match List.nth_opt fn_param_ml_tys_orig i with
          | Some param_ty ->
            let rec count_arrows = function
              | Miniml.Tarr (_, rest) -> 1 + count_arrows rest
              | _ -> 0
            in
            let expected = count_arrows param_ty in
            let actual = Mlutil.nb_lams ml_arg in
            if expected > 0 && actual > expected then
              let outer_ids, inner_body =
                Mlutil.collect_n_lams expected ml_arg
              in
              let barrier =
                Mlutil.named_lams outer_ids (MLmagic inner_body)
              in
              (* Compute the return type from the substituted param type by
                 stripping [expected] top-level arrows.  The remaining type
                 is the function-typed codomain that the inner lambda
                 implements.

                 When the substituted codomain is still a [Tvar] (happens
                 when [tys = []] so substitution is a no-op), use the
                 [concrete_tvar_type] computed above — it holds the
                 concrete [T1] type derived from the excess args and the
                 enclosing function's return type. *)
              let ret_ty =
                match List.nth_opt fn_param_ml_tys i with
                | Some subst_pt ->
                  let rec codomain_after n = function
                    | Miniml.Tarr (_, rest) when n > 0 ->
                      codomain_after (n - 1) rest
                    | ty -> ty
                  in
                  let ret_ml = codomain_after expected subst_pt in
                  ( match resolve_tmeta ret_ml with
                  | Miniml.Tvar _ | Miniml.Tvar' _ -> concrete_tvar_type
                  | _ ->
                    Some (convert_ml_type_to_cpp_type
                            env Refset'.empty tvars ret_ml) )
                | None -> None
              in
              (barrier, ret_ty)
            else
              (ml_arg, None)
          | None -> (ml_arg, None) )
        | _ -> (ml_arg, None)
      in
      let expr = gen_expr env ml_arg in
      (* Annotate the outer lambda with the explicit return type computed
         during the split, so that C++ concept checking sees the concrete
         [std::function<...>] return type instead of the raw closure type. *)
      let expr =
        match split_ret_ty, expr with
        | Some ret_ty, CPPlambda (params, None, body, cap) ->
          CPPlambda (params, Some ret_ty, body, cap)
        | _ -> expr
      in
      let expr =
        match (List.nth_opt fn_param_ml_tys i, expr) with
        | Some param_ty, CPPlambda (params, ret_opt, body, cap) ->
          let param_cpp_ty =
            convert_ml_type_to_cpp_type env Refset'.empty tvars param_ty
          in
          ( match param_cpp_ty with
          | Tfun (_, Tunique_ptr inner) ->
            let rec wrap_stmt = function
              | Sreturn (Some e) ->
                Sreturn (Some (CPPfun_call (CPPmk_unique inner, [e])))
              | s -> map_stmt Fun.id wrap_stmt Fun.id s
            in
            CPPlambda
              (params, Some (Tunique_ptr inner), List.map wrap_stmt body, cap)
          | _ -> expr )
        | _ -> expr
      in
      (* Wrap void calls as values only when the expression will be used
         as a value (not in monadic parameter handler which places it in
         statement position inside a lambda). *)
      let as_value () =
        match ml_arg with
        | MLapp (f, _) when ml_callee_is_void f ->
          (* Don't wrap eta-expanded lambdas (partial applications) — they
             are function VALUES, not void call results. *)
          ( match expr with
          | CPPlambda _ -> expr
          | _ -> wrap_void_call_as_value expr )
        | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
          ( match expr with
          | CPPlambda _ -> expr
          | _ -> wrap_void_call_as_value expr )
        | _ -> expr
      in
      match List.nth_opt fn_param_ml_tys i with
      | Some param_ty
        when ml_body_returns_erased_field ml_arg
             && not (match param_ty with
                     | Miniml.Tglob (g, _, _) -> Table.is_promoted_type_var g
                     | _ -> false) ->
        let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars param_ty in
        CPPany_cast (cpp_ty, as_value ())
      (* Monadic parameter (reified mode only): the callee expects
         [shared_ptr<ITree<R>>].  If the argument already produces a reified
         tree, pass through as-is; otherwise wrap in [ITree<R>::ret()]. *)
      | Some param_ty when tctx.itree_mode = Reified
          && is_monadic_ml_type param_ty
          && not (is_reified_monadic_expr ml_arg) ->
        Table.require_itree_header ();
        let r_ml = extract_itree_result_ml param_ty in
        let r_cpp = convert_ml_type_to_cpp_type env Refset'.empty tvars r_ml in
        (* Voidify unit result type in ITree wrapper *)
        let r_cpp = if ml_type_is_unit r_ml then Tvoid else r_cpp in
        let itree_ty = mk_itree_type r_cpp in
        let ret_expr = mk_itree_ret_for_value r_cpp r_ml expr in
        (* Void/unit effects need their side-effect evaluated before ret(). *)
        let body =
          if r_cpp = Tvoid || ml_type_is_unit_or_void r_ml then
            [Sexpr expr; Sreturn (Some ret_expr)]
          else
            [Sreturn (Some ret_expr)]
        in
        CPPfun_call (CPPlambda ([], Some itree_ty, body, false), [])
      (* Void-ified function reference passed as callback to polymorphic
         HOF where the ORIGINAL (non-substituted) parameter codomain is a
         type variable (not concrete unit).  The C++ definition uses a
         template type parameter for MapsTo (e.g. MapsTo<T1, unsigned int>),
         so the void function needs wrapping to return std::monostate.
         When the original codomain IS concrete unit, the C++ definition
         already uses MapsTo<void, ...> which accepts void-returning fns. *)
      | Some param_ty
        when (match ml_arg with
              | MLglob (r, _) | MLmagic (MLglob (r, _)) -> is_void_ified_ref r
              | _ -> false)
             && (match param_ty with Miniml.Tarr _ -> true | _ -> false)
             && ml_type_is_unit (ml_codomain param_ty)
             && (match List.nth_opt fn_param_ml_tys_orig i with
                 | Some orig_pt ->
                   not (ml_type_is_unit (ml_codomain orig_pt))
                 | None -> false) ->
        let dom_mls =
          let rec collect acc = function
            | Miniml.Tarr (t, rest) ->
              ( match resolve_tmeta t with
              | Miniml.Tdummy _ -> collect acc rest
              | t -> collect (t :: acc) rest )
            | _ -> List.rev acc
          in
          collect [] param_ty
        in
        let dom_cpps =
          List.map
            (fun t -> convert_ml_type_to_cpp_type env Refset'.empty tvars t)
            dom_mls
        in
        let params =
          List.mapi
            (fun j ty ->
              (Tref (Tmod (TMconst, ty)), Some (Id.of_string (Printf.sprintf "_wa%d" j))))
            dom_cpps
        in
        let args =
          List.rev_map (fun (_, id) -> CPPvar (Option.get id)) params
        in
        let body =
          [ Sexpr (CPPfun_call (expr, args));
            Sreturn (Some (mk_tt_expr ())) ]
        in
        CPPlambda (List.rev params, None, body, false)
      | _ -> as_value ()
    ) regular_ml_args in
    let ty = fn_ml_ty_subst in
    let ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ty in
    (* Combine: instance types first, then regular type args. If any regular
       type arg is Tany or a dummy type glob (from erased params), drop ALL
       regular type args via filter_erased_type_args and let the compiler deduce
       them. See filter_erased_type_args for why we must drop all args rather
       than just the erased ones.

       Exception: when the callee's return type depends on an erased type var,
       C++ can't deduce it from lambda arguments (lambdas don't participate in
       template argument deduction). In that case, recover the concrete type
       from the enclosing function's return type. *)
    let regular_type_args =
      List.map
        (fun ty ->
          let t =
            convert_ml_type_to_cpp_type env Refset'.empty tvars (type_simpl ty)
          in
          if has_unnamed_tvar t then
            Tglob (GlobRef.VarRef (Id.of_string "dummy_type"), [], [])
          else
            t )
        tys
    in
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
      let filtered = filter_erased_type_args regular_type_args in
      (* Check if the callee's return type is a Tvar pointing to an erased
         (Tdummy Ktype) domain position, and if so, return the position index,
         the concrete C++ type to use, and the full ML domain. *)
      let try_recover_erased_return_type () =
        let rec resolve_tmeta = function
          | Miniml.Tmeta {contents = Some t} -> resolve_tmeta t
          | t -> t
        in
        match tctx.current_cpp_return_type with
        | None -> None
        | Some ret_ty ->
        match find_type_opt id with
        | None -> None
        | Some ml_ty_orig ->
          let ret = resolve_tmeta (ml_return_type ml_ty_orig) in
          ( match ret with
          | Miniml.Tvar i | Miniml.Tvar' i ->
            let rec collect_dom acc = function
              | Miniml.Tarr (t1, t2) -> collect_dom (resolve_tmeta t1 :: acc) t2
              | _ -> List.rev acc
            in
            let all_dom = collect_dom [] ml_ty_orig in
            (* Tvar uses 1-based indexing (matching type_subst_list); convert to
               0-based for list access. *)
            let idx = i - 1 in
            if idx >= 0 && idx < List.length all_dom then
              match
                List.nth all_dom idx
              with
              | Miniml.Tdummy Miniml.Ktype -> Some (idx, ret_ty, all_dom)
              | _ -> None
            else
              None
          | _ -> None )
      in
      if filtered = [] && regular_type_args <> [] then
        (* Case (a): tys was non-empty but all got filtered. Only attempt
           recovery when there are no non-erased value args — if there are value
           args, C++ can deduce the template types from them (and injecting
           explicit type args may conflict with the template signature, e.g.
           hk_map's F0/F1 are function types). *)
          match
            if args = [] then try_recover_erased_return_type () else None
          with
        | Some (idx, ret_ty, _) ->
          (* Replace the erased position with the concrete return type, then
             filter out any remaining erased entries. *)
          List.mapi (fun j t -> if j = idx then ret_ty else t) regular_type_args
          |> List.filter (fun t -> not (is_erased_type t))
        | None -> filtered
      else if tys = [] then
        (* Case (b): tys is empty — synthesize type args from scratch. Build one
           entry per Tdummy Ktype domain position.

           Recovery is attempted when:
           - [args = []] — no value args, so C++ can't deduce types.
           - [concrete_tvar_type <> None] — the callee's return type [Tvar]
             was resolved from excess args + enclosing return type. *)
        let should_recover = args = [] || concrete_tvar_type <> None in
          match
            if should_recover then try_recover_erased_return_type () else None
          with
        | Some (_idx, _ret_ty, all_dom) ->
          (* Use [concrete_tvar_type] when available (excess args case),
             otherwise fall back to the enclosing function's return type. *)
          let t1 = match concrete_tvar_type with
            | Some t -> t
            | None -> _ret_ty
          in
          List.filter_map
            (function
              | Miniml.Tdummy Miniml.Ktype -> Some t1
              | _ -> None )
            all_dom
        | None -> filtered
      else
        filtered
    in
    (* Promoted type vars ([Tvar(1000, Some name)]) are no longer separate
       template parameters — they're resolved through typeclass instance
       access (e.g. [typename _tcI0::Obj]) by [gen_dfun]'s promoted var
       resolution.  No additional template type arguments are needed at
       call sites. *)
    let promoted_type_args = [] in
    (* Filter out Tvoid entries from typeclass_type_args — these arise from
       skipped infrastructure (e.g. ReSum instances) that we classified as
       typeclass args just to remove them from regular_ml_args. They should
       not become actual template type parameters. *)
    let typeclass_type_args =
      List.filter (fun t -> t <> Tvoid) typeclass_type_args
    in
    let all_type_args =
      typeclass_type_args @ regular_type_args @ promoted_type_args
    in
    let cglob = mk_cppglob id all_type_args in
    (* Check if this is a typeclass instance used as a type (for :: access).
       When all args are consumed (domain and args both empty after filtering),
       return just the type reference, not a function call. This avoids
       generating numOption<numNat, unsigned int>() instead of numOption<numNat,
       unsigned int> for qualified access like ::to_nat. *)
    let id_is_typeclass_instance = ref_returns_typeclass id in
    (* {b Curried excess args.}  When a call site provides more value args
       than the callee's ML type has arrows, the extras are curried onto the
       result: [f(primary_args)(excess_args)].

       This is valid when the callee genuinely returns a function:
       - Its codomain is a type alias ([Tglob]) that may expand to [Tarr]
         (e.g. [State S A = S -> A * S]).
       - Its codomain is a type variable ([Tvar]) that, after instantiation
         with the call-site type args [tys], becomes [Tarr] (e.g.
         [fold_right] with [B = nat -> nat]).
       - It is an inlined custom constant (e.g. [fst], [snd]).

       When the codomain is a type variable that instantiates to a
       non-function type (e.g. [div2_rect] with [T1 = R_div2]), the excess
       args come from proof-certificate functions ([Function] vernacular
       [_correct] terms) that are never called at runtime.  We emit an abort
       placeholder for those. *)
    let wrap_excess base =
      if excess_args = [] then
        base
      else (
        let ret_is_chainable =
          is_inline_custom id
          ||
          match find_type_opt id with
          | Some ml_ty ->
            let cod = ml_codomain ml_ty in
            ( match resolve_tmeta cod with
            | Miniml.Tglob _ -> true
            | Miniml.Tarr _ -> true
            | Miniml.Tvar _ ->
              (* Type variable: instantiate with the call-site type args to
                 determine if the return type is actually a function.
                 [cod] is already the function's codomain (all arrows
                 stripped), so after substitution we check [cod_inst]
                 directly — NOT [ml_codomain cod_inst], which would strip
                 another layer of arrows and reject valid cases like
                 [fold_right] instantiated at [A = nat -> nat].

                 When [tys] is empty (type args carried as [MLdummy] in
                 [args] rather than in the [MLglob] type-arg list),
                 substitution is a no-op and the [Tvar] stays unresolved.
                 In this case, chain unconditionally: Rocq's type system
                 guarantees that excess {i value} args (non-[MLdummy]) can
                 only exist when the return type instantiates to a function.
                 Proof-level excess args are already removed by the
                 [MLdummy] filter above. *)
              if tys = [] then
                true
              else
                let cod_inst = Mlutil.type_subst_list tys cod in
                ( match resolve_tmeta cod_inst with
                | Miniml.Tarr _ -> true
                | Miniml.Tglob _ -> true
                | _ -> false )
            | _ -> false )
          | None -> false
        in
        if ret_is_chainable then
          CPPfun_call (base, List.rev (List.map (gen_expr env) excess_args))
        else
          CPPabort "untranslatable curried proof term" )
    in
    let primary_result =
      match ty with
      | Tfun (dom, cod) ->
        (* Filter domain to exclude type class types (they're now template
           params) and erased types. Use has_hkt_erasure for deep checking:
           proof params like wf witnesses may extract as function types
           containing dummy_type (e.g. Tfun([List<T1>], dummy_type)) rather than
           plain dummy_type. These entries must be removed to match the ML arg
           list which already filters out MLdummy entries. *)
        let dom =
          List.filter
            (fun t ->
              (not (Table.is_typeclass_type_cpp t))
              && not (is_erased_type t)
              && not (is_skipped_cpp_type t) )
            dom
        in
        let missing_args = get_eta_args dom args in
        (* When excess args exist (from the ML-level arity split above), do
           NOT eta-expand even if the flattened C++ type has more domain
           elements than ML args.  The mismatch occurs when the callee's
           return type is itself a function type (e.g. [fst] returning
           [Obj -> Path<Obj>]): convert_ml_type_to_cpp_type merges the
           return-type arrows into the domain, inflating [dom_len] beyond the
           ML-level arity.  The excess args will be chained by [wrap_excess]
           below. *)
        if missing_args == [] || excess_args <> [] then
          if (id_is_typeclass_instance || is_inline_custom id) && args = [] then
            (* Typeclass instance or zero-arg inline custom — return
               the glob directly so the template renders as-is. *)
            cglob
          else
            CPPfun_call (cglob, List.rev args)
        else
          (* Substitute promoted type vars in eta-expanded lambda params. When
             partially applying a function like pick_op<nat_magma>, the domain
             types may contain Tvar(1000, Some "carrier") — a promoted type var.
             We resolve these to the concrete type from the typeclass instance
             (e.g., unsigned int from nat_magma::carrier). *)
          let missing_args, cod =
            if typeclass_ml_args <> [] && missing_args <> [] then
              let subst_map =
                List.concat_map
                  (fun tc_arg ->
                    match tc_arg with
                    | MLglob (r, _) ->
                      let bindings = Table.get_instance_promoted_types r in
                      List.map
                        (fun (var_name, ml_ty) ->
                          let cpp_ty =
                            convert_ml_type_to_cpp_type
                              env
                              Refset'.empty
                              tvars
                              ml_ty
                          in
                          (var_name, cpp_ty) )
                        bindings
                    | _ -> [] )
                  typeclass_ml_args
              in
              if subst_map <> [] then
                let rec subst_promoted = function
                  | Tvar (1000, Some name) ->
                    ( match
                        List.find_opt
                          (fun (vid, _) -> Id.equal vid name)
                          subst_map
                      with
                    | Some (_, concrete) -> concrete
                    | None -> Tvar (1000, Some name) )
                  | Tmod (m, t) -> Tmod (m, subst_promoted t)
                  | Tfun (d, c) ->
                    Tfun (List.map subst_promoted d, subst_promoted c)
                  | Tshared_ptr t -> Tshared_ptr (subst_promoted t)
                  | t -> t
                in
                (List.map subst_promoted missing_args, subst_promoted cod)
              else
                (missing_args, cod)
            else
              (missing_args, cod)
          in
          let eta_args =
            List.mapi
              (fun i ty ->
                let wrapped =
                  match ty with
                  | Tshared_ptr _ | Tunique_ptr _ -> Tref (Tmod (TMconst, ty))
                  | _ -> ty
                in
                (wrapped, Some (eta_param_id i)) )
              missing_args
          in
          (* When eta_keep_moves is set (single-use closure from MLletin),
             keep CPPmove wrappers and capture by reference for zero-copy.
             Otherwise strip CPPmove recursively: the closure may be called
             multiple times, so captured variables must not be consumed.
             A top-level strip is insufficient when moves appear inside
             constructor calls, e.g. cons(std::move(t1), rest) — those
             moves would fire on the closure's own captured copy on every
             invocation. *)
          let rec strip_moves_deep = function
            | CPPmove inner -> strip_moves_deep inner
            | CPPfun_call (f, fargs) ->
              CPPfun_call (f, List.map strip_moves_deep fargs)
            | e -> e
          in
          let captured_args =
            if eta_keep_moves then args
            else List.map strip_moves_deep args
          in
          let call_args =
            captured_args
            @ List.mapi (fun i _ -> CPPvar (eta_param_id i)) eta_args
          in
          let call = CPPfun_call (cglob, List.rev call_args) in
          let ret_ty, body =
            if cod = Tvoid then
              (* Void-returning function: execute for side effects, then
                 return without a value. *)
              (None, [Sexpr call; Sreturn None])
            else
              (Some cod, [Sreturn (Some call)])
          in
          CPPlambda (List.rev eta_args, ret_ty, body, not eta_keep_moves)
      | _ ->
        if id_is_typeclass_instance && args = [] then
          cglob
        else if is_inline_custom id && args = [] then
          (* Zero-arg inline custom: return the glob directly so the
             template string renders as-is, without an appended (). *)
          cglob
        else
          CPPfun_call (cglob, args)
    in
    (* Collapse identity inline customs (%a0) at AST level.  This prevents
       unnecessary IIFE wrapping when a void call passes through an identity
       wrapper (e.g. Ceval) and then appears in statement position. *)
    let primary_result =
      match primary_result with
      | CPPfun_call (CPPglob (_, _, Some ci), [single_arg])
        when ci.ci_inline = Some "%a0" ->
        single_arg
      | _ -> primary_result
    in
    wrap_excess primary_result
  | _ ->
    (* Non-global callee (e.g., a local variable from MLrel). Filter out MLdummy
       args — these are erased type/prop parameters that have no runtime
       representation. Unlike the MLglob case above, there is no type-arg list
       to filter here; we only need to drop value-level dummies. *)
    let args =
      List.filter
        (fun x ->
          match x with
          | MLdummy _ -> false
          | _ -> true )
        args
    in
    let args = List.map (fun x ->
      match x with
      | MLapp (f, _) | MLmagic (MLapp (f, _)) when ml_callee_is_void f ->
        wrap_void_call_as_value (gen_expr env x)
      | _ -> gen_expr env x) args in
    (* Detect over-application: when a local variable's C++ type has fewer
       value-domain arrows than the number of ML args, the call must be split
       into a primary call and a chained application of excess args. Example: [f
       : A -> State S B] applied as [f(a, s')] becomes [f(a)(s')]. *)
    let n_value_dom =
      match f with
      | MLrel i ->
        (try count_ml_value_arrows (get_env_type i) with _ -> List.length args)
      | _ -> List.length args
    in
    let n_args = List.length args in
    if n_args = 0 then
      (* All args were erased (MLdummy): no function call, just the
         expression itself.  This arises when erased proof arguments
         (e.g. [le n 0] in [Function]-generated [_rect] bodies) are
         applied to a local variable — the proofs are filtered out,
         leaving an empty arg list.  Generating [f()] would be wrong
         because the C++ type has no 0-arg overload. *)
      gen_expr env f
    else if n_args < n_value_dom && n_value_dom > 0 then
      (* Under-application (partial application due to proof erasure).
         The callee expects [n_value_dom] args but only [n_args] are
         provided — the rest were erased proofs in the same
         [MLapp] that have been filtered out.

         Generate a lambda wrapper that captures the provided args and
         forwards them along with fresh parameters for the remaining
         args.  E.g., [f2(n1)] where [f2 : (nat, T1) -> T1] becomes:
         [[&](T1 _pa0) { return f2(n1, _pa0); }]. *)
      let remaining_ml_tys =
        match f with
        | MLrel i ->
          ( try
              let ml_ty = get_env_type i in
              (* Skip [n_args] non-dummy domain entries to find the
                 remaining value-domain types. *)
              let rec skip_and_collect n = function
                | Miniml.Tarr (t, rest) ->
                  ( match resolve_tmeta t with
                  | Miniml.Tdummy _ -> skip_and_collect n rest
                  | t ->
                    if n > 0 then skip_and_collect (n - 1) rest
                    else t :: skip_and_collect 0 rest )
                | Miniml.Tmeta {contents = Some t} -> skip_and_collect n t
                | _ -> []
              in
              skip_and_collect n_args ml_ty
            with _ -> [] )
        | _ -> []
      in
      if remaining_ml_tys <> [] then
        let callee = gen_expr env f in
        let tvars = get_current_type_vars () in
        let pa_params = List.mapi (fun j ml_ty ->
          let cpp_ty = convert_ml_type_to_cpp_type
                         env Refset'.empty tvars ml_ty in
          (cpp_ty, Some (Id.of_string (Printf.sprintf "_pa%d" j))) )
          remaining_ml_tys
        in
        let pa_exprs = List.map (fun (_, id_opt) ->
          CPPvar (Option.get id_opt)) pa_params in
        (* CPPlambda stores params in reverse (de Bruijn) order;
           the printer reverses them for display.  Reverse pa_params
           so the printed output matches source order. *)
        CPPlambda (List.rev pa_params, None,
          [Sreturn (Some (CPPfun_call (callee,
              List.rev (args @ pa_exprs))))],
          true)
      else
        CPPfun_call (gen_expr env f, List.rev args)
    else if n_args > n_value_dom && n_value_dom > 0 then
      let primary = List.rev (safe_firstn n_value_dom args) in
      let excess = List.rev (List.skipn n_value_dom args) in
      CPPfun_call (CPPfun_call (gen_expr env f, primary), excess)
    else
      (* Check whether this call returns [std::any] (erased type) but the
         enclosing function expects a concrete type, requiring an
         [std::any_cast<T>] wrapper.  See [ml_codomain_erases_to_any].
         Two callee forms are handled:
         - [MLcase] single-branch record projection whose field type has a
           higher-rank codomain (e.g. [apply : forall A, A -> A] stored as
           [std::function<std::any(std::any)>]).
         - [MLrel] higher-rank callback whose env-type has a [Tvar] codomain
           guarded by [Tdummy] (e.g. [f : forall A, A -> A]). *)
      let result = CPPfun_call (gen_expr env f, List.rev args) in
      let n = n_args in
      let erased_cod =
        match f with
        | MLcase (case_ty, _, pv) when Array.length pv = 1 ->
          let (binds, _, _, br_body) = pv.(0) in
          let n_binds = List.length binds in
          let proj_idx =
            match br_body with
            | MLrel i when i >= 1 && i <= n_binds -> Some (n_binds - i)
            | MLmagic (MLrel i) when i >= 1 && i <= n_binds -> Some (n_binds - i)
            | _ -> None
          in
          ( match proj_idx with
          | Some idx ->
            ( match case_ty with
            | Tglob (r, _, _) ->
              let all_ft = Table.record_field_types r in
              let non_erased = filter_value_types all_ft in
              ( try ml_codomain_erases_to_any n (List.nth non_erased idx)
                with _ -> false )
            | _ -> false )
          | None -> false )
        | MLrel i ->
          ( try ml_codomain_erases_to_any n (get_env_type i) with _ -> false )
        | _ -> false
      in
      ( match (erased_cod, tctx.current_cpp_return_type) with
      | (true, Some ty) when ty <> Tany && not (is_erased_type ty) && ty <> Tvoid ->
        CPPany_cast (ty, result)
      | _ -> result )

(** Build the qualified constructor struct type for a pattern match branch.

    For [list<int>::Cons], this produces
    [Tqualified(Tnamespace(r, Tglob(r, temps, \[\])), ctor_name)].
    Local inductives omit the namespace wrapper to avoid double qualification. *)
and ctor_type_of_match env (typ : ml_type) (cname : GlobRef.t) : cpp_type =
  let tvars = get_current_type_vars () in
  let ctor_name = ctor_struct_id_of_ref cname in
  match typ with
  | Tglob (r, tys, _) ->
    let tys = List.map type_simpl tys in
    let tys =
      match r with
      | GlobRef.IndRef (kn, _) ->
        ( match Table.get_ind_num_param_vars_opt kn with
        | Some num_param_vars -> safe_firstn num_param_vars tys
        | None -> tys )
      | _ -> tys
    in
    let temps = build_template_params env tvars tys in
    let is_local_ind =
      List.exists
        (Environ.QGlobRef.equal Environ.empty_env r)
        (get_local_inductives ())
    in
    let ind_type =
      if is_local_ind then Tglob (r, temps, [])
      else Tnamespace (r, Tglob (r, temps, []))
    in
    Tqualified (ind_type, ctor_name)
  | _ -> Tid (ctor_name, [])

(** Generate a single branch of an {!Smatch} if/else-if pattern match chain.

    Produces an {!smatch_branch} record whose body statements live directly
    in the enclosing if-block.

    {b Structured bindings.}  Field accesses use
    [const auto& [d_f0, d_f1] = std::get<T>(v)].  The reference binding is
    required so that [[=]]-capturing closures copy the struct value rather
    than a raw pointer that could dangle after the match scope ends.

    {b [match_i] suffix generation.}  [match_i] is the match-level counter
    (0 for the outermost match).  Nested matches increment the counter so
    binding names get suffixed (e.g. [d_a00], [d_a10]) to avoid shadowing
    outer bindings.

    {b [dummies] mask.}  A [bool list] parallel to [ids]: [true] means the
    pattern variable is actually used (gets a binding); [false] means it is
    [Dummy] (omitted from the structured binding with a placeholder).  This
    avoids generating unused variable warnings in the C++ output.

    @param env      current name environment
    @param typ      the scrutinee's ML type (used to resolve the inductive)
    @param rty      the branch's return type
    @param cname    the constructor's [GlobRef.t]
    @param ids      renamed pattern variable names with types
    @param dummies  parallel mask: [true] = non-Dummy (used), [false] = Dummy
    @param body     the branch body AST
    @param sname    scrutinee expression name (for structured binding access)
    @param match_i  nesting level counter for name suffixing
    @param scrut_v  the [scrut->v()] or [scrut.v()] accessor expression *)
and gen_match_branch env (typ : ml_type) rty cname ids dummies body sname
    match_i scrut_v ~is_value_type ~is_owned ~scrut_db =
  let ctor_type = ctor_type_of_match env typ cname in
  let ctor_name = ctor_struct_id_of_ref cname in
  let ctor_struct_name = Id.to_string ctor_name in
  let n_pat_vars = List.length ids in
  (* When the scrutinee is an owned variable (is_owned = true) and we create
     const-ref structured bindings into it ([const auto& [d_a0, d_a1] = ...]),
     moving the scrutinee inside the branch would leave those references
     dangling.  Exclude the shifted scrutinee index from move_owned_vars for
     the duration of the branch so move insertion cannot fire on it. *)
  let exclude_scrutinee =
    if is_owned then Option.map (fun db -> db + n_pat_vars) scrut_db
    else None
  in
  let body_stmts =
    with_shifted_move_tracking n_pat_vars ~clear_dead:true
      ?exclude_owned:exclude_scrutinee
      (fun () ->
      let saved_match_counter = tctx.match_param_counter in
      let saved_cs_counter = tctx.cs_counter in
      let saved_return_type = tctx.current_cpp_return_type in
      (* Prevent void optimisation from leaking into match branches: the branch
         body lives inside an IIFE that returns the match result type, not the
         enclosing function's void.  Clear return type to stop gen_stmts from
         emitting bare [return;] for unit values. *)
      ( if tctx.current_cpp_return_type = Some Tvoid then
          tctx.current_cpp_return_type <- None );
      let body_stmts = gen_stmts env (fun x -> Sreturn (Some x)) body in
      tctx.current_cpp_return_type <- saved_return_type;
      tctx.match_param_counter <- saved_match_counter;
      tctx.cs_counter <- saved_cs_counter;
      body_stmts)
  in
  (* Compute structured binding names for ALL constructor fields.
     For match_i=0 the binding name equals the struct field name (e.g. [d_a0]);
     for deeper nesting a numeric suffix avoids shadowing outer bindings
     (e.g. [d_a00] at level 1, [d_a01] at level 2). *)
  let suffix =
    if match_i = 0 then "" else string_of_int (match_i - 1)
  in
  let tvars = get_current_type_vars () in
  let rev_ids = List.rev ids in
  let dummies_arr = Array.of_list dummies in
  (* Convert field types using the inductive's ns to correctly identify
     unique_ptr fields (self-references). *)
  let ind_ref =
    match cname with
    | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
    | r -> r
  in
  (* To detect which fields are unique_ptr in the struct definition,
     check the definition-site field types (ip_types) for self-references.
     A field is unique_ptr iff its definition-site type starts with
     Tglob(parent_ref, ...). Using ind_ns on the concrete match type is
     wrong for parametric types like pair(A, B) where a field B could
     happen to be pair<C,D> without being recursive. *)
  let def_site_field_tys =
    match Table.get_ctor_ip_types_opt cname with
    | Some tys -> tys
    | None -> []
  in
  (* ip_types includes ALL constructor argument types, including Prop-erased
     ones (Tdummy).  The struct fields and pattern variables skip erased
     entries.  So the i-th pattern variable corresponds to the i-th NON-ERASED
     entry in def_site_field_tys, not def_site_field_tys[i] directly.
     Pre-filter Tdummy entries so field_is_self/is_uniform use the right index. *)
  let non_erased_def_site_field_tys =
    List.filter (fun t -> not (isTdummy t)) def_site_field_tys
  in
  (* Extract the MutInd key from ind_ref for mutual sibling detection *)
  let ind_kn_opt =
    match ind_ref with
    | GlobRef.IndRef (kn, _) -> Some kn
    | _ -> None
  in
  let is_self_or_mutual r =
    Environ.QGlobRef.equal Environ.empty_env r ind_ref
    || match r, ind_kn_opt with
       | GlobRef.IndRef (kn2, _), Some kn ->
         MutInd.CanOrd.equal kn2 kn
       | _ -> false
  in
  let field_is_self_or_mutual_ref_at_def i =
    match List.nth_opt non_erased_def_site_field_tys i with
    | Some (Miniml.Tglob (r, _, _)) -> is_self_or_mutual r
    | Some (Miniml.Tmeta {contents = Some (Miniml.Tglob (r, _, _))}) ->
      is_self_or_mutual r
    | _ -> false
  in
  (* Does the def-site ML type contain a self/mutual reference nested
     inside type arguments (e.g. list(tree(A)) when defining tree)? *)
  let rec ml_has_self_ref = function
    | Miniml.Tglob (r, args, _) ->
      is_self_or_mutual r || List.exists ml_has_self_ref args
    | Miniml.Tmeta {contents = Some t} -> ml_has_self_ref t
    | Miniml.Tarr (t1, t2) ->
      ml_has_self_ref t1 || ml_has_self_ref t2
    | _ -> false
  in
  let field_has_nested_self_ref_at_def i =
    match List.nth_opt non_erased_def_site_field_tys i with
    | Some (Miniml.Tglob (r, args, _)) when not (is_self_or_mutual r) ->
      List.exists ml_has_self_ref args
    | Some (Miniml.Tmeta {contents = Some (Miniml.Tglob (r, args, _))})
      when not (is_self_or_mutual r) ->
      List.exists ml_has_self_ref args
    | _ -> false
  in
  let field_bindings =
    List.mapi
      (fun i (_var_name, ml_ty) ->
        let field_id = lookup_ctor_field_name ctor_struct_name i in
        let binding_name =
          Id.of_string (Id.to_string field_id ^ suffix)
        in
        (* A field needs dereferencing if:
           1. It's a direct self/mutual ref at the definition site
              (stored as shared_ptr in the struct), OR
           2. The def-site field type is Tvar (type parameter) that resolves
              to shared_ptr<T> via template substitution, where T is a
              value-type inductive in method_self_ns.  This happens when a
              container like List<shared_ptr<tree>> stores elements via
              template parameter t_A = shared_ptr<tree>. Direct struct
              fields (Tglob at def-site) are bare value types. *)
        (* Convert using empty ns.  For value-type self/mutual fields the
           expression substituted into the branch body is dereferenced, but the
           structured binding itself still has the stored field type
           [shared_ptr<T>].  Loopify uses this metadata to infer frame field
           types for expressions like [d_a0.get()] and [*d_a0]. *)
        let bare_field_cpp_ty =
          convert_ml_type_to_cpp_type env Refset'.empty tvars ml_ty
        in
        let storage_field_cpp_ty =
          convert_ml_type_to_cpp_type
            env
            (Refset'.add ind_ref Refset'.empty)
            tvars
            ml_ty
        in
        (* A field is unique_ptr only for UNIFORM self-recursion.  Non-uniform
           recursion (e.g. tree<pair<T,T>> inside tree<T>) uses shared_ptr.
           Find the self/mutual reference anywhere in the ML type (direct or
           nested in type args) and check if its type arguments match the
           parent's params uniformly. *)
        let is_uniform_self_ref_at_def i =
          let rec find_self_ref_args = function
            | Miniml.Tglob (r, args, _) when is_self_or_mutual r -> Some args
            | Miniml.Tglob (_, args, _) ->
              List.find_map find_self_ref_args args
            | Miniml.Tmeta {contents = Some t} -> find_self_ref_args t
            | _ -> None
          in
          match List.nth_opt non_erased_def_site_field_tys i with
          | Some ty -> begin
            match find_self_ref_args ty with
            | Some args ->
              let n_params = Table.get_ctor_num_param_vars cname in
              List.length args = n_params
              && List.for_all (fun (j, arg) ->
                match arg with
                | Miniml.Tvar k | Miniml.Tvar' k -> k = j + 1
                | Miniml.Tmeta {contents = Some (Miniml.Tvar k)}
                | Miniml.Tmeta {contents = Some (Miniml.Tvar' k)} -> k = j + 1
                | _ -> false
              ) (List.mapi (fun j a -> (j, a)) args)
            | None -> true  (* no self-ref found: treat as uniform *)
          end
          | _ -> true
        in
        let is_unique_ptr =
          ( field_is_self_or_mutual_ref_at_def i
            || field_has_nested_self_ref_at_def i )
          && not (Table.is_coinductive ind_ref)
          && is_uniform_self_ref_at_def i
        in
        let field_cpp_ty =
          if is_unique_ptr then Tunique_ptr bare_field_cpp_ty
          else
            (* Use storage_field_cpp_ty but correct false-positive unique_ptr
               or shared_ptr wrapping: when storage says unique_ptr/shared_ptr
               but the def-site check says NOT a self-ref, use bare type instead.
               This happens when a type parameter is instantiated to the same
               inductive (e.g. element List<T> inside List<List<T>>): the element
               field's def-site type is a bare Tvar (not self-ref), but at the
               use site it resolves to List<T> which ns-wraps to shared_ptr. *)
            match storage_field_cpp_ty with
            | (Tunique_ptr _ | Tshared_ptr _) when
                non_erased_def_site_field_tys <> []
                && not (field_is_self_or_mutual_ref_at_def i)
                && not (field_has_nested_self_ref_at_def i) ->
              bare_field_cpp_ty
            | _ -> storage_field_cpp_ty
        in
        (* For coinductive types, fields with nested self-refs are stored
           as shared_ptr to break circular template dependencies (e.g.
           colist<cotree<A>> inside cotree<A>).  Apply the same wrapping
           that gen_ind_header_v2 applies. *)
        let field_cpp_ty =
          if Table.is_coinductive ind_ref
             && field_has_nested_self_ref_at_def i
          then Tshared_ptr bare_field_cpp_ty
          else field_cpp_ty
        in
        let used = dummies_arr.(i) in
        (binding_name, field_cpp_ty, is_unique_ptr, used))
      rev_ids
  in
  let field_bindings_arr = Array.of_list field_bindings in
  let rec expr_has_lambda = function
    | CPPfun_call (CPPlambda (_, _, body, _), _) ->
      (* IIFE: lambda is invoked immediately, so reference captures are safe.
         Only check the lambda body for nested non-IIFE lambdas. *)
      List.exists stmt_has_lambda body
    | CPPlambda _ -> true
    | e ->
      let found = ref false in
      iter_expr_children
        ~on_expr:(fun e' -> if expr_has_lambda e' then found := true)
        ~on_stmts:(fun stmts ->
          if List.exists stmt_has_lambda stmts then found := true)
        e;
      !found
  and stmt_has_lambda = function
    | Sreturn (Some e) | Sexpr e -> expr_has_lambda e
    | Sasgn (_, _, e) | Sderef_asgn (_, e) -> expr_has_lambda e
    | Sif (c, t, f) ->
      expr_has_lambda c || List.exists stmt_has_lambda t
      || List.exists stmt_has_lambda f
    | Sswitch (scrut, _, branches, default) ->
      expr_has_lambda scrut
      || List.exists (fun (_, body) -> List.exists stmt_has_lambda body) branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Smatch (branches, default) ->
      List.exists
        (fun br ->
          expr_has_lambda br.smb_scrutinee
          || List.exists stmt_has_lambda br.smb_body)
        branches
      || (match default with
          | Some body -> List.exists stmt_has_lambda body
          | None -> false)
    | Scustom_case (_, scrut, _, branches, _) ->
      expr_has_lambda scrut
      || List.exists
           (fun (_, _, body) -> List.exists stmt_has_lambda body)
           branches
    | Sassign_field (obj, _, e) -> expr_has_lambda obj || expr_has_lambda e
    | Swhile (c, body) -> expr_has_lambda c || List.exists stmt_has_lambda body
    | Sblock body -> List.exists stmt_has_lambda body
    | Sblock_custom (_, _, _, _, args, _) -> List.exists expr_has_lambda args
    | _ -> false
  in
  let branch_has_lambda = List.exists stmt_has_lambda body_stmts in
  (* True when the enclosing function returns a coinductive type and will
     wrap each branch result in a [lazy_] thunk via [cofix_wrap].  The
     thunk is a [CPPlambda] that captures by [=], so any [unique_ptr]
     binding reachable from the branch body would be illegally captured.
     This flag triggers pre-extraction even when [branch_has_lambda] is
     false (because the lambda is added externally by [inline_iife]). *)
  let return_type_is_coinductive =
    match tctx.current_cpp_return_type with
    | Some (Tglob (r, _, _)) -> Table.is_coinductive r
    | _ -> false
  in
  let branch_needs_uptr_preextract =
    branch_has_lambda || return_type_is_coinductive
  in
  (* Substitute pattern variable references with the structured-binding
     names.  For unique_ptr fields (self-references at definition site),
     the structured binding gives [const unique_ptr<T>& d_field]; we
     dereference it so the body sees a value reference [const T&] instead.
     This ensures method calls use [.] not [->]. *)
  let body_stmts =
    List.fold_left
      (fun stmts (i, (var_name, _ml_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, is_uptr, _) = field_bindings_arr.(i) in
          let bare_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars _ml_ty in
          (* A field may be stored as unique_ptr either because is_uptr detected
             a self-ref via ip_types (Crane-extracted types), or because the field
             type itself is Tunique_ptr (custom-mapped types like stdlib list whose
             ip_types are not registered).  In both cases, when the branch body
             contains a lambda (or the return type is coinductive, meaning
             cofix_wrap adds a lambda externally), we must pre-extract the value
             before the lambda to avoid capturing the non-copyable unique_ptr
             via [=]. *)
          let is_uptr_field =
            is_uptr || (match field_ty with Tunique_ptr _ -> true | _ -> false)
          in
          let subst_expr =
            if is_uptr_field && branch_needs_uptr_preextract then
              CPPvar (Id.of_string (Id.to_string binding_name ^ "_value"))
            else if is_uptr_field then CPPderef (CPPvar binding_name)
            else if field_ty <> bare_ty
                    && contains_shared_ptr_or_unique_ptr field_ty then
              gen_clone_field_expr ~src_ty:field_ty ~dst_ty:bare_ty
                (CPPvar binding_name)
            else
              CPPvar binding_name
          in
          List.map (local_var_subst_stmt var_name subst_expr) stmts
        else
          stmts )
      body_stmts
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let uptr_value_bindings =
    List.filter_map
      (fun (i, (_var_name, ml_ty)) ->
        if dummies_arr.(i) then
          let (binding_name, field_ty, is_uptr, _) =
            field_bindings_arr.(i)
          in
          let is_uptr_field =
            is_uptr || (match field_ty with Tunique_ptr _ -> true | _ -> false)
          in
          if is_uptr_field && branch_needs_uptr_preextract then
            let bare_ty =
              convert_ml_type_to_cpp_type env Refset'.empty tvars ml_ty
            in
            let value_id =
              Id.of_string (Id.to_string binding_name ^ "_value")
            in
            let clone =
              gen_clone_field_expr
                ~src_ty:(Tunique_ptr bare_ty) ~dst_ty:bare_ty
                (CPPvar binding_name)
            in
            Some (Sasgn (value_id, Some bare_ty, clone))
          else None
        else None)
      (List.mapi (fun i x -> (i, x)) rev_ids)
  in
  let body_stmts = uptr_value_bindings @ body_stmts in
  (* For fields stored as [std::any] (erased type indices in type-indexed
     inductives such as [wrap : Set -> Type]), wrap direct returns of those
     bindings with [std::any_cast<rty>].

     A struct field is [std::any] when [gen_ind_header_v2] erases its type:
     this happens when a field's ML type is a [Tvar] that references a type
     INDEX (not a kept PARAMETER), so it has no C++ template name and
     [tvar_erase_type] converts it to [Tany].  The pattern variable's ML type
     is NOT a reliable indicator — the Tmeta reconstructor resolves it to a
     concrete type in monomorphic contexts, masking the [std::any] storage.

     We only fix DIRECT [return <binding>;] statements.  When the binding is
     passed to a higher-rank callback (e.g. the auto-generated [wrap_rect]),
     the field is forwarded as [std::any] unchanged; the existing
     [ml_codomain_erases_to_any] mechanism handles the cast on the call result. *)
  let body_stmts =
    match Table.get_ctor_ip_types_opt cname with
    | None -> body_stmts
    | Some ip_tys ->
      let cast_ty_opt =
        let t = convert_ml_type_to_cpp_type env Refset'.empty tvars rty in
        if type_is_erased t then None else Some t
      in
      ( match cast_ty_opt with
      | None -> body_stmts
      | Some cast_ty ->
        (* Identify which field bindings are stored as std::any in C++.
           A field is std::any iff gen_ind_header_v2 would erase its type.
           gen_ind_header_v2 uses only PARAMETER type vars (not index vars)
           and applies tvar_erase_type when param_vars is empty — making
           any Tvar that references an index (rather than a parameter)
           collapse to Tany.  We replicate that computation here. *)
        let num_param_vars = Table.get_ctor_num_param_vars cname in
        let param_vars =
          List.map Common.tparam_name
            (List.firstn num_param_vars (Table.get_ind_ip_vars cname))
        in
        let ind_ref =
          match cname with
          | GlobRef.ConstructRef ((kn, i), _) -> GlobRef.IndRef (kn, i)
          | r -> r
        in
        let ind_ns = Refset'.add ind_ref Refset'.empty in
        let non_dummy_ip_tys = List.filter (fun t -> not (isTdummy t)) ip_tys in
        let erased_names =
          List.mapi (fun i (bn, _, _, _) ->
              match List.nth_opt non_dummy_ip_tys i with
              | Some ip_ty ->
                let cpp_ty =
                  convert_ml_type_to_cpp_type (empty_env ()) ind_ns param_vars ip_ty
                in
                let cpp_ty =
                  if param_vars = [] then tvar_erase_type cpp_ty else cpp_ty
                in
                if is_erased_type cpp_ty then Some bn else None
              | None -> None)
            field_bindings
          |> List.filter_map Fun.id
        in
        if erased_names = [] then body_stmts
        else
          List.map (function
            | Sreturn (Some (CPPvar id))
              when List.exists (Id.equal id) erased_names ->
              Sreturn (Some (CPPany_cast (cast_ty, CPPvar id)))
            | s -> s )
            body_stmts )
  in
  (* Use std::get (smb_var = Some) when any constructor field is actually used;
     otherwise use holds_alternative only (smb_var = None). *)
  let has_used_fields = List.exists Fun.id dummies in
  { smb_scrutinee = scrut_v;
    smb_ctor_type = ctor_type;
    smb_var = (if has_used_fields then Some sname else None);
    smb_field_bindings =
      (if has_used_fields then
         List.map (fun (n, ty, _is_uptr, used) -> (n, ty, used)) field_bindings
       else []);
    smb_extra_conds = [];
    smb_reuse = None;
    smb_is_value_type = is_value_type;
    smb_is_owned = is_owned;
    smb_body = body_stmts }

(** Generate C++ pattern matching for an [MLcase].

    Dispatches based on the inductive's structure:
    - {b Enum types}: generate a [switch] statement on tag values
      ({!gen_enum_branches}).
    - {b Variant types}: generate an if/else-if chain using
      [std::holds_alternative] guards and [std::get] structured bindings
      ({!gen_match_branch}).
    - {b Reuse optimization}: when the scrutinee is an owned [shared_ptr] with
      [use_count() == 1] and a branch constructs a value of the same type/arity,
      mutate the existing allocation in-place instead of allocating a new one
      ({!Escape.find_reuse_candidates}).

    {b Type resolution.}  When the match type contains unresolved [Tvar]s,
    attempts to resolve them from [env_types] so that field types and
    constructor type parameters are concrete for code generation. *)
and gen_cpp_case (typ : ml_type) t env pv =
  (* When the match type annotation has unresolved Tvars, try to resolve from
     context. This handles monomorphic functions where MLcase has Tvar but the
     concrete type is known. *)
  let resolve_tvar_type typ candidate =
    match (typ, candidate) with
    | Miniml.Tglob (r1, _, _), Miniml.Tglob (r2, _, _)
      when Environ.QGlobRef.equal Environ.empty_env r1 r2
           && has_tvar typ
           && not (has_tvar candidate) -> candidate
    | _ -> typ
  in
  let typ =
    match t with
    | MLrel i | MLmagic (MLrel i) ->
      (* Scrutinee is a variable reference — use its concrete type. Try
         env_types first (correctly tracks let-bound variables with shifted de
         Bruijn indices), then fall back to param_types. Unwrap Tmeta wrappers
         since env_types may store types in Tmeta form. *)
      let rec unwrap_tmeta = function
        | Miniml.Tmeta {contents = Some t} -> unwrap_tmeta t
        | t -> t
      in
      let env_ty_opt =
        try
          let env_ty = unwrap_tmeta (get_env_type i) in
          match env_ty with
          | Miniml.Tglob _ -> Some env_ty
          | _ -> None
        with _ -> None
      in
      ( match env_ty_opt with
      | Some let_ty -> resolve_tvar_type typ let_ty
      | None ->
      match get_param_type_by_index i with
      | Some (Miniml.Tglob _ as param_ty) -> resolve_tvar_type typ param_ty
      | _ -> typ )
    | MLapp (func_expr, _) | MLmagic (MLapp (func_expr, _)) ->
      (* Scrutinee is a function call — use function's return type *)
      let func_ref =
        match func_expr with
        | MLglob (r, _) | MLmagic (MLglob (r, _)) -> Some r
        | _ -> None
      in
      ( match func_ref with
      | Some r ->
        ( match find_type_opt r with
        | Some ty ->
          let ret_ty = ml_return_type ty in
          resolve_tvar_type typ ret_ty
        | None -> typ )
      | None -> typ )
    | _ -> typ
  in
  (* Check if this is an enum inductive type *)
  let is_enum =
    match typ with
    | Miniml.Tglob (GlobRef.IndRef (kn, i), _, _) ->
      is_enum_inductive (GlobRef.IndRef (kn, i))
    | _ -> false
  in
  if is_enum then (* Generate switch-based matching wrapped in IIFE *)
    let ind_ref =
      match typ with
      | Miniml.Tglob (r, _, _) -> r
      | _ ->
        CErrors.anomaly (Pp.str "gen_case_cpp: enum type expected to be Tglob")
    in
    let scrutinee = gen_expr env t in
    let rec gen_enum_branches = function
      | [] -> []
      | (ids, _rty, p, body) :: cs ->
      match p with
      | Pusual r | Pcons (r, _) ->
        let _ids', env' =
          push_vars'
            (List.rev_map
               (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
               ids )
            env
        in
        let ctor_name =
          Id.of_string (Common.enum_ctor_name (Common.pp_global_name Type r))
        in
        let body_stmts = gen_stmts env' (fun x -> Sreturn (Some x)) body in
        (ctor_name, body_stmts) :: gen_enum_branches cs
      | Pwild | Prel _ | Ptuple _ -> gen_enum_branches cs
    in
    let gen_default_stmts () =
      let wild_br =
        Array.to_list pv
        |> List.find_opt (fun (_, _, p, _) -> match p with Pwild -> true | _ -> false)
      in
      match wild_br with
      | Some (_, _, _, body) ->
        Some (gen_stmts env (fun x -> Sreturn (Some x)) body)
      | None -> None
    in
    let tvars = get_current_type_vars () in
    (* Compute IIFE return type.  Void: [-> void] is required when the lambda
       may have no return statement.  Function-typed ([Tfun _]): emit the
       explicit [std::function<R(A...)>] type so that branches returning
       distinct lambda closure types can all be implicitly converted via
       [std::function]'s converting constructor; without it, C++ cannot deduce
       a common return type from distinct closures.  Other non-void: [None]
       lets C++ deduce, which avoids leaking unresolved Tvars (e.g. [T1])
       from the ML type annotation into non-template contexts. *)
    let iife_ret_opt =
      let branch_rty =
        match Array.to_list pv with
        | (_, rty, _, _) :: _ -> rty
        | [] -> typ
      in
      let r = convert_ml_type_to_cpp_type env Refset'.empty tvars branch_rty in
      if is_cpp_unit_type r
         || ml_type_is_unit (ml_result_type branch_rty)
      then Some Tvoid
      else match r with
        | Tfun _ -> Some r
        | _ -> None
    in
    let saved_ret = tctx.current_cpp_return_type in
    if iife_ret_opt = Some Tvoid then
      tctx.current_cpp_return_type <- Some Tvoid;
    let branches = gen_enum_branches (Array.to_list pv) in
    let default = gen_default_stmts () in
    tctx.current_cpp_return_type <- saved_ret;
    CPPfun_call
      (CPPlambda ([], iife_ret_opt, [Sswitch (scrutinee, ind_ref, branches, default)], false), [])
  else
    (* Generate if/else-if pattern matching using [std::holds_alternative]
       and [std::get].  Produces an {!Smatch} node wrapped in
       an IIFE.  When the scrutinee is an owned [shared_ptr] with reuse
       candidates, a reuse branch is prepended with a
       [use_count() == 1] guard. *)
    let reuse_candidates = Escape.find_reuse_candidates typ pv in
    let scrut_db =
      match t with
      | MLrel i -> Some i
      | MLmagic (MLrel i) -> Some i
      | _ -> None
    in
    let is_coinductive = is_coinductive_type typ in
    (* Allocate a unique [_m] name for this match level.  All branches of
       the same match reuse this name (each [if (auto* _m = ...)] creates
       its own scope); nested matches get the next name ([_m0], [_m1]). *)
    let match_i = tctx.match_param_counter in
    tctx.match_param_counter <- match_i + 1;
    let sname =
      Id.of_string
        ( if match_i = 0 then "_m"
          else "_m" ^ string_of_int (match_i - 1) )
    in
    (* Generate scrutinee expression.  Clear [move_dead_after] to prevent
       [std::move(x)->v()] use-after-move — the scrutinee is referenced
       across all branches. *)
    let saved_dead_visit = tctx.move_dead_after in
    tctx.move_dead_after <- Escape.IntSet.empty;
    let scrut_expr = gen_expr env t in
    tctx.move_dead_after <- saved_dead_visit;
    (* Methodification rewrites the receiver parameter to [this] (or [*this]
       when the value is needed).  Ownership analysis may still mark the
       original parameter as owned, but a const method cannot decompose the
       receiver through [v_mut()].  Treat receiver matches as borrowed so
       generated access goes through [v()]. *)
    let scrut_is_owned =
      match scrut_expr with
      | CPPthis | CPPderef CPPthis -> false
      | _ -> (
        match scrut_db with
        | Some i -> Escape.IntSet.mem i tctx.move_owned_vars
        | None -> false )
    in
    (* Build variant accessor.  All inductives (including coinductives)
       are value types and use [scrut.v()] (dot access).  Exception:
       [this] is always a pointer, so method bodies use [this->v()]. *)
    let scrut_is_ptr =
      match scrut_expr with CPPthis -> true | _ -> false
    in
    let scrut_v =
      if scrut_is_ptr then
        CPPmethod_call (scrut_expr, Id.of_string "v", [])
      else
        CPPfun_call (CPPmember (scrut_expr, Id.of_string "v"), [])
    in
    (* Push renamed pattern variables into the environment, register their
       types in [env_types], and compute a dummies mask (true = non-Dummy).
       The caller is responsible for saving/restoring env_types. *)
    let process_match_pattern_vars ids env =
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      push_env_types ids';
      let dummies =
        List.map (fun (x, _) -> match x with Dummy -> false | _ -> true) ids
      in
      (ids', env', dummies)
    in
    (* Generate one {!smatch_branch} per constructor pattern, collecting
       a wildcard body from [Pwild] / [Prel]. *)
    let rec gen_branches = function
      | [] -> ([], None)
      | (ids, rty, p, body) :: cs ->
      match p with
      | Pusual r | Pcons (r, _) ->
        let saved_env_types = tctx.env_types in
        let ids', env', dummies = process_match_pattern_vars ids env in
        let br =
          gen_match_branch env' typ rty r ids' dummies body sname
            match_i scrut_v
            ~is_value_type:true
            ~is_owned:scrut_is_owned
            ~scrut_db
        in
        tctx.env_types <- saved_env_types;
        let rest, wild = gen_branches cs in
        (br :: rest, wild)
      | Pwild | Prel _ ->
        let body_stmts =
          gen_stmts env (fun x -> Sreturn (Some x)) body
        in
        ([], Some body_stmts)
      | Ptuple _ -> gen_branches cs
    in
    let branches, wildcard = gen_branches (Array.to_list pv) in
    (* Prepend a reuse branch when the scrutinee is an owned [shared_ptr]
       with reuse candidates.  The branch checks
       [holds_alternative<Ctor>(scrut->v()) && scrut.use_count() == 1],
       then mutates the variant storage in place and returns the original
       pointer — avoiding a fresh allocation. *)
    let branches =
      (* Reuse optimization only applies to shared_ptr types (coinductive).
         Value types don't have reference counting. *)
      if false && reuse_candidates <> [] && scrut_is_owned && not is_coinductive then
        let tvars = get_current_type_vars () in
        let pv_idx, variant_idx, matched_ctor, _arity, _tail_ctor, tail_args =
          List.hd reuse_candidates
        in
        let reuse_ctor_struct_name = ctor_struct_name_of_ref matched_ctor in
        let ids, _rty, _pat, body = pv.(pv_idx) in
        (* Safety check: skip reuse if the scrutinee is referenced anywhere
           in the branch body.

           The reuse path [std::move]'s fields out of the scrutinee before
           evaluating tail constructor arguments.  If any tail arg, prefix
           [let]-binding RHS, or lambda capture references the scrutinee —
           directly or through a function call — the moved-from fields
           produce null dereferences ([reuse_use_after_move],
           [reuse_fn_in_body], [reuse_lambda_capture]) or self-referential
           cycles ([reuse_self_cycle]).

           {!Escape.nb_occur_match} counts occurrences of a de Bruijn
           index in a MiniML term.  In the branch body scope, pattern
           variables occupy indices [1..n_pat_vars], so the scrutinee
           sits at [db + n_pat_vars]. *)
        let n_pat_vars = List.length ids in
        let scrutinee_used_in_body =
          match scrut_db with
          | Some db -> Escape.nb_occur_match (db + n_pat_vars) body > 0
          | None -> true
        in
        if scrutinee_used_in_body then branches
        else
        (* use_count() == 1 guard *)
        let use_count_cond =
          CPPbinop ("==",
            CPPfun_call (CPPmember (scrut_expr, Id.of_string "use_count"), []),
            CPPint 1)
        in
        (* Push pattern variables into the environment.  Wrap the entire
           body generation in {!with_shifted_move_tracking} to shift
           [move_owned_vars] and [move_dead_after] indices by [n_pat_vars].
           This matches the index shift performed by the non-reuse path,
           preventing parameter-level indices from colliding with
           pattern-variable indices and causing spurious [std::move]s
           ([reuse_move_shadow]). *)
        let saved_env_types = tctx.env_types in
        let rf_var = Id.of_string "_rf" in
        let ids', env', dummies, extract_stmts, prefix_stmts, assign_stmts =
          with_shifted_move_tracking n_pat_vars ~clear_dead:true (fun () ->
        let ids', env', dummies = process_match_pattern_vars ids env in
        (* Extract fields into local variables via [std::move(_rf.d_field)] *)
        let rev_ids' = List.rev ids' in
        let extract_stmts =
          List.filter_map Fun.id
            (List.mapi
               (fun i (var_name, ml_ty) ->
                 let cpp_ty =
                   convert_ml_type_to_cpp_type env Refset'.empty tvars ml_ty
                 in
                 if List.nth dummies i then
                   let field_id =
                     lookup_ctor_field_name reuse_ctor_struct_name i
                   in
                   Some
                     (Sasgn
                        ( var_name, Some cpp_ty,
                          CPPmove (CPPmember (CPPvar rf_var, field_id)) ))
                 else None )
               rev_ids')
        in
        (* Walk through MLletin/MLmagic to reach the tail MLcons, generating
           statements for each intermediate binding. *)
        let rec gen_prefix_and_tail env' body =
          match body with
          | MLcons (_, _, _) -> ([], env')
          | MLmagic a -> gen_prefix_and_tail env' a
          | MLletin (x, t, a, b) ->
            let x' = remove_prime_id (id_of_mlid x) in
            let _, env'' = push_vars' [(x', t)] env' in
            let afun v = Sasgn (x', None, v) in
            let asgn = gen_stmts env' afun a in
            push_env_types [(x', t)];
            let letin_stmt =
              match asgn with
              | [Sasgn (x', None, e)] ->
                [Sasgn (x', Some (convert_ml_type_to_cpp_type env
                   Refset'.empty tvars t), e)]
              | _ ->
                Sdecl (x', convert_ml_type_to_cpp_type env Refset'.empty tvars t)
                :: asgn
            in
            let rest, final_env = gen_prefix_and_tail env'' b in
            (letin_stmt @ rest, final_env)
          | _ -> ([], env')
        in
        let prefix_stmts, body_env = gen_prefix_and_tail env' body in
        (* Assign new field values back.  Skip erased proof/type fields
           ([MLdummy]) — their value is semantically irrelevant (the C++
           type is [std::any]) and the field already holds a valid value
           from the original construction. *)
        let assign_stmts =
          List.filter_map
            (fun (i, tail_arg) ->
              match tail_arg with
              | MLdummy _ | MLmagic (MLdummy _) -> None
              | _ ->
                let field_id =
                  lookup_ctor_field_name reuse_ctor_struct_name i
                in
                Some (Sassign_field (CPPvar rf_var, field_id,
                        gen_expr body_env tail_arg)))
            (List.mapi (fun i a -> (i, a)) tail_args)
        in
        (ids', env', dummies, extract_stmts, prefix_stmts, assign_stmts))
        in
        tctx.env_types <- saved_env_types;
        (* Build reuse body: extract fields, prefix lets,
           assign new values, return original pointer.
           The [auto& _rf = std::get<Type>(scrut->v_mut())] binding is
           emitted at print time using [smb_ctor_type], not baked into
           the stmt list. *)
        (* Skip reuse when there are no field assignments — the tail
           constructor has the same fields as the matched one (typically a
           zero-field constructor like Nil→Nil).  The use_count check would
           be pure overhead since we're not actually mutating anything. *)
        if assign_stmts = [] && extract_stmts = [] && prefix_stmts = [] then
          branches
        else
          let needs_rf = assign_stmts <> [] in
          let reuse_body =
            extract_stmts @ prefix_stmts @ assign_stmts
            @ [Sreturn (Some scrut_expr)]
          in
          List.mapi (fun i br ->
            if i = pv_idx then
              { br with smb_reuse = Some (use_count_cond,
                  (if needs_rf then Some rf_var else None),
                  reuse_body) }
            else br
          ) branches
      else
        branches
    in
    (* Compute IIFE return type.  Void: [-> void] is required when the lambda
       may have no return statement.  Function-typed ([Tfun _]): emit the
       explicit [std::function<R(A...)>] type so that branches returning
       distinct lambda closure types can all be implicitly converted via
       [std::function]'s converting constructor; without it, C++ cannot deduce
       a common return type from distinct closures.  Other non-void: [None]
       lets C++ deduce, which avoids leaking unresolved Tvars (e.g. [T1])
       from the ML type annotation into non-template contexts. *)
    let tvars = get_current_type_vars () in
    let iife_ret_opt =
      let branch_rty =
        match Array.to_list pv with
        | (_, rty, _, _) :: _ -> rty
        | [] -> typ
      in
      let r = convert_ml_type_to_cpp_type env Refset'.empty tvars branch_rty in
      if is_cpp_unit_type r
         || ml_type_is_unit (ml_result_type branch_rty)
      then Some Tvoid
      else match r with
        | Tfun _ -> Some r
        | _ -> None
    in
    CPPfun_call
      ( CPPlambda ([], iife_ret_opt,
          [Smatch (branches, wildcard)], false),
        [] )

(** Generate a custom match body using user-provided custom extraction syntax.
    Wraps the body in a lambda with pattern-bound variables for std::visit. *)
and gen_cpp_custom_body env k rty ids body =
  let tvars = get_current_type_vars () in
  let ret = convert_ml_type_to_cpp_type env Refset'.empty tvars rty in
  let ids =
    List.map
      (fun (x, ty) ->
        (x, convert_ml_type_to_cpp_type env Refset'.empty tvars ty) )
      (List.rev ids)
  in
  let body = gen_stmts env k body in
  (ids, ret, body)

(** Test whether a C++ expression is "trivial" — a simple variable or member
    access that can safely be duplicated without side effects.  Non-trivial
    expressions (function calls, constructor applications, etc.) should be
    cached in a temporary when the custom match template uses [%scrut] more
    than once. *)
and is_trivial_scrut = function
  | CPPvar _ | CPPget _ | CPPget' _ | CPParrow _ | CPPmember _
  | CPPqualified _ | CPPderef _ | CPPenum_val _ | CPPglob _ -> true
  | _ -> false

(** Generate a custom case expression using user-provided extraction syntax.
    Entry point for custom pattern match generation.
    Returns a [cpp_stmt list]: when the scrutinee is non-trivial and the
    template uses [%scrut] more than once, a cache declaration
    [auto _cs = expr;] is prepended before the [Scustom_case] node. *)
and gen_custom_cpp_case env k (typ : ml_type) t pv =
  let tvars = get_current_type_vars () in
  let temps =
    match typ with
    | Tglob (r, tys, _) -> build_template_params env tvars tys
    | _ -> []
  in
  let typ = convert_ml_type_to_cpp_type env Refset'.empty tvars typ in
  (* Custom match templates may use %scrut multiple times (e.g., option: "if
     (%scrut.has_value()) { ... *%scrut; ... }"). Each occurrence re-prints the
     scrutinee C++ expression, so any std::move in the scrutinee would fire
     multiple times. Suppress moves when the template duplicates the
     scrutinee. *)
  let cmatch = find_custom_match pv in
  let scrut_uses =
    let plen = 6 in
    (* length of "%scrut" *)
    let n = String.length cmatch in
    let rec count i acc =
      if i + plen > n then
        acc
      else if String.sub cmatch i plen = "%scrut" then
        count (i + plen) (acc + 1)
      else
        count (i + 1) acc
    in
    count 0 0
  in
  let saved_dead = tctx.move_dead_after in
  if scrut_uses > 1 then
    tctx.move_dead_after <- Escape.IntSet.empty;
  let t = gen_expr env t in
  tctx.move_dead_after <- saved_dead;
  (* When the template uses %scrut more than once and the scrutinee is a
     non-trivial expression (function call, constructor, etc.), cache it in
     a temporary to avoid double evaluation. *)
  let scrut, cache_prefix =
    if scrut_uses > 1 && not (is_trivial_scrut t) then
      let n = tctx.cs_counter in
      tctx.cs_counter <- n + 1;
      let cache_id =
        Id.of_string (if n = 0 then "_cs" else "_cs" ^ string_of_int n)
      in
      (CPPvar cache_id, [Sasgn (cache_id, Some Ttodo, t)])
    else
      (t, [])
  in
  let rec gen_cases = function
    | [] -> []
    | (ids, rty, p, t) :: cs ->
    match p with
    | Pusual r | Pcons (r, _) ->
      let ids', env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      let n_pat_vars = List.length ids in
      let saved_env_types = tctx.env_types in
      let saved_owned = tctx.move_owned_vars in
      push_env_types ids';
      let br =
        with_shifted_move_tracking n_pat_vars (fun () ->
          gen_cpp_custom_body env' k rty ids' t)
      in
      tctx.env_types <- saved_env_types;
      tctx.move_owned_vars <- saved_owned;
      br :: gen_cases cs
    | Pwild | Prel _ | Ptuple _ -> gen_cases cs
  in
  cache_prefix @
  [Scustom_case (typ, scrut, temps, gen_cases (Array.to_list pv), cmatch)]

(** {2 IIFE Inlining}

    When [gen_expr] wraps multi-statement code in an immediately-invoked
    function expression (IIFE):
    {[
      [&]() \{
        unsigned int x = p->px;
        unsigned int y = p->py;
        return (x + y);
      \}()
    ]}
    and the result is consumed at statement level (e.g. by [Sreturn] or
    [Sasgn]), the lambda wrapper is unnecessary.  {!inline_iife} detects
    this pattern and flattens the body statements, replacing the final
    [return] with the enclosing continuation:
    {[
      unsigned int x = p->px;
      unsigned int y = p->py;
      return (x + y);
    ]}
    This produces more readable C++ and avoids interfering with compiler
    optimisations (e.g. copy elision / RVO through a lambda boundary). *)

(** Extract block template info from an inline custom expression.
    Returns [Some(ref, template, args, tyargs)] if the expression is
    an inline custom whose template contains [%result]. *)
and extract_block_template = function
  | CPPglob (ref, tys, Some ci) -> begin
    match ci.ci_inline with
    | Some tmpl when Common.contains_substring tmpl "%result" ->
      Some (ref, tmpl, [], tys)
    | _ -> None
    end
  | CPPfun_call (CPPglob (ref, tys, Some ci), args) -> begin
    match ci.ci_inline with
    | Some tmpl when Common.contains_substring tmpl "%result" ->
      Some (ref, tmpl, List.rev args, tys)
    | _ -> None
    end
  | _ -> None

(** [inline_iife k expr] checks whether [expr] is an IIFE
    ([CPPfun_call(CPPlambda(\[\], _, body, _), \[\])]).  If so, it replaces
    the final [Sreturn(Some v)] in [body] with [k v] and returns the
    inlined statement list.  Otherwise it falls back to [\[k expr\]].

    Only zero-argument, zero-parameter IIFEs are inlined — parameterised
    lambdas and those with explicit return-type annotations involving
    captures are left untouched, since they may have name-scoping or
    type-deduction side-effects.

    @param k     the statement-level continuation (e.g. [Sreturn], [Sasgn])
    @param expr  the expression produced by [gen_expr] *)
and inline_iife (k : cpp_expr -> cpp_stmt) = function
  | CPPfun_call (CPPlambda ([], ret_ty, body, _), []) when body <> [] ->
    let k_is_return =
      match k (CPPint 0) with Sreturn _ -> true | _ -> false
    in
    if not k_is_return then
      (* Non-return continuations (e.g. Sasgn for let-bindings) keep the
         IIFE to prevent name clashes between variables from separately
         inlined IIFEs in the same block scope. *)
      [k (CPPfun_call (CPPlambda ([], ret_ty, body, false), []))]
    else
    (* Replace each [Sreturn(Some v)] in the IIFE body with [k(v)] and
       emit the body statements directly, eliminating the lambda wrapper.

       Since k is guaranteed to produce [Sreturn], inlining into
       [Sswitch] and [Scustom_case] is safe — [return] preserves the
       "exit the enclosing case" semantics.  [Sif] is always safe
       because if/else branches are mutually exclusive. *)
    let map_all_or_none transform branches =
      let results = List.map transform branches in
      if List.for_all (fun x -> x <> None) results then
        Some (List.filter_map Fun.id results)
      else None
    in
    let rec replace_last_return = function
      | [Sreturn (Some v)] -> Some [k v]
      | [Sreturn None] -> None  (* void return — cannot apply k *)
      | [Sif (c, then_br, else_br)] ->
        ( match (replace_last_return then_br, replace_last_return else_br) with
        | Some then_br', Some else_br' -> Some [Sif (c, then_br', else_br')]
        | _ -> None )
      | [Sswitch (scrut, ind_ref, branches, default)] ->
        let default' =
          match default with
          | Some stmts -> ( match replace_last_return stmts with
            | Some stmts' -> Some (Some stmts')
            | None -> None )
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun (id, stmts) ->
              match replace_last_return stmts with
              | Some stmts' -> Some (id, stmts')
              | None -> None )
            branches, default')
        with
        | Some branches', Some default' -> Some [Sswitch (scrut, ind_ref, branches', default')]
        | _ -> None )
      | [Scustom_case (ty, scrut, tyargs, branches, cmatch)] ->
        ( match map_all_or_none
            (fun (args, bty, stmts) ->
              match replace_last_return stmts with
              | Some stmts' -> Some (args, bty, stmts')
              | None -> None )
            branches
        with
        | Some branches' ->
          Some [Scustom_case (ty, scrut, tyargs, branches', cmatch)]
        | None -> None )
      | [Smatch (branches, default)] ->
        let default' =
          match default with
          | Some stmts -> ( match replace_last_return stmts with
            | Some stmts' -> Some (Some stmts')
            | None -> None )
          | None -> Some None
        in
        ( match (map_all_or_none
            (fun br ->
              match replace_last_return br.smb_body with
              | Some body' -> Some { br with smb_body = body' }
              | None -> None )
            branches, default')
        with
        | Some branches', Some default' ->
          Some [Smatch (branches', default')]
        | _ -> None )
      | stmt :: rest when rest <> [] ->
        ( match replace_last_return rest with
        | Some rest' -> Some (stmt :: rest')
        | None -> None )
      | _ -> None
    in
    ( match replace_last_return body with
    | Some stmts -> stmts
    | None -> [k (CPPfun_call (CPPlambda ([], ret_ty, body, false), []))] )
  | expr -> [k expr]

(** Escape analysis for local fixpoint variables.

    Determines whether [target_id] appears in any position other than the
    callee of a direct call [CPPfun_call(CPPvar target_id, args)].  If so,
    the fixpoint "escapes" and must use the [shared_ptr<std::function>]
    pattern (see {!gen_local_fix_shared_ptr}) instead of the simpler [\[&\]]
    capture pattern (see {!gen_local_fix_by_ref}).

    Escape positions include: function argument, constructor field, return
    value, record field, or binding RHS.

    Lambda bodies are treated conservatively: {b any} reference to the
    fixpoint inside a lambda body — even in call position — counts as an
    escape.  This is because the lambda captures the [std::function] value,
    and a [\[&\]]-captured [std::function]'s internal lambda still holds
    dangling stack references when the lambda outlives the fixpoint's scope.

    @param target_id  The fixpoint variable to track.
    @param stmts      The statement list (typically the continuation after
                      the fixpoint's let-binding) to scan.
    @return [true] if the fixpoint escapes. *)
and fixpoint_escapes_in_stmts target_id stmts =
  let rec check_expr e =
    match e with
    | CPPfun_call (CPPvar id, args) when Id.equal id target_id ->
      (* Safe: direct call.  But check the arguments for escapes. *)
      List.exists check_expr args
    | CPPvar id when Id.equal id target_id ->
      true  (* Escape: bare reference outside call position *)
    | CPPlambda (_, _, body, _) ->
      (* Any reference inside a lambda means the fixpoint is captured.
         Even if only called, the capture copies the std::function whose
         internal lambda still has dangling [&] references.
         Must use a properly recursive walker since map_expr/map_stmt
         only do one level of descent. *)
      let rec has_var_in_expr e =
        match e with
        | CPPvar id when Id.equal id target_id -> true
        | _ ->
          let found = ref false in
          let fe e' = if not !found then found := has_var_in_expr e'; e' in
          let fs s' = if not !found then found := has_var_in_stmt s'; s' in
          ignore (Minicpp.map_expr fe fs Fun.id e);
          !found
      and has_var_in_stmt s =
        let found = ref false in
        let on_expr e = if not !found then found := has_var_in_expr e in
        let on_stmts ss =
          if not !found then found := List.exists has_var_in_stmt ss
        in
        Minicpp.iter_stmt_children ~on_expr ~on_stmts s;
        !found
      in
      List.exists has_var_in_stmt body
    | _ ->
      (* Recurse into sub-expressions *)
      let found = ref false in
      let fe e = if not !found then found := check_expr e; e in
      ignore (Minicpp.map_expr fe Fun.id Fun.id e);
      !found
  in
  let rec check_stmt s =
    let found = ref false in
    let on_expr e = if not !found then found := check_expr e in
    let on_stmts ss = if not !found then found := check_stmts ss in
    Minicpp.iter_stmt_children ~on_expr ~on_stmts s;
    !found
  and check_stmts ss = List.exists check_stmt ss
  in
  check_stmts stmts

(** Generate local fixpoint declarations using the [\[&\]]-capture pattern.

    Used when {!fixpoint_escapes_in_stmts} returns [false], meaning the
    fixpoint variable is only used in direct call position and never
    escapes into a closure or data structure.  The [\[&\]] capture is
    lightweight (no heap allocation, no indirection) but creates dangling
    references if the closure outlives the enclosing scope.

    Generated C++:
    {v
      std::function<R(A...)> f;
      f = [&](A... args) { ... f(args) ... };
    v}

    @return [(decls, defs)] — declaration and definition statement lists.
    @see gen_local_fix_shared_ptr for the escaping-fixpoint alternative. *)
and gen_local_fix_by_ref env renamed_ids funs_with_params =
  let tvars = get_current_type_vars () in
  let fix_func_type ty =
    match ty with
    | Minicpp.Tfun (params, Minicpp.Tvar (_, None)) ->
      Minicpp.Tfun (params, Minicpp.Tvoid)
    | _ -> ty
  in
  let ret_ty ty =
    match convert_ml_type_to_cpp_type env Refset'.empty tvars ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (_, None) -> None
      | _ -> Some t )
    | _ -> None
  in
  let decls =
    List.map
      (fun (id, ty) ->
        Sdecl
          ( id,
            fix_func_type
              (convert_ml_type_to_cpp_type env Refset'.empty tvars ty) ) )
      renamed_ids
  in
  let defs =
    List.map2
      (fun (id, _fty) (args, body) ->
        Sasgn
          ( id,
            None,
            CPPlambda
              ( List.map
                  (fun (id, ty) ->
                    ( convert_ml_type_to_cpp_type env Refset'.empty tvars ty,
                      Some id ) )
                  args,
                ret_ty _fty,
                body,
                false ) ) )
      renamed_ids funs_with_params
  in
  (decls, defs)

(** Generate local fixpoint declarations using the shared_ptr fixpoint
    pattern for escaping fixpoints.

    Used when {!fixpoint_escapes_in_stmts} returns [true], meaning the
    fixpoint variable is captured by a closure, stored in a data structure,
    or otherwise outlives its defining scope.  The [\[=\]] capture copies the
    [shared_ptr] into the lambda, keeping the [std::function] alive on the
    heap.  Recursive calls dereference the shared pointer before invoking.

    Generated C++ (schematic):
    - [auto f = make_shared<function<R(A...)>>()] allocates the shared cell.
    - [*f = \[=\](A... args) mutable { ... }] assigns the closure body.
    - Inside the closure, the recursive call dereferences [f] before invoking.

    The lambda is marked [mutable] because the captured [shared_ptr] must be
    non-const to allow the internal [std::function] to be invoked.

    @return [(decls, defs, deref_subst)] where [deref_subst] is a function
    that rewrites [CPPvar fix_id] to [CPPderef(CPPvar fix_id)] in a
    statement list, so that call sites in the continuation use the
    dereferenced form.
    @see gen_local_fix_by_ref for the non-escaping alternative.
    @see Minicpp.Sderef_asgn for the dereference assignment node. *)
and gen_local_fix_shared_ptr env renamed_ids funs_with_params =
  let tvars = get_current_type_vars () in
  let fix_func_type ty =
    match ty with
    | Minicpp.Tfun (params, Minicpp.Tvar (_, None)) ->
      Minicpp.Tfun (params, Minicpp.Tvoid)
    | _ -> ty
  in
  let deref_subst stmts =
    List.fold_left
      (fun s (fix_id, _) ->
        List.map
          (local_var_subst_stmt
             fix_id
             (CPPraw ("(*" ^ Id.to_string fix_id ^ ")")))
          s )
      stmts renamed_ids
  in
  let ret_ty ty =
    match convert_ml_type_to_cpp_type env Refset'.empty tvars ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (_, None) -> None
      | _ -> Some t )
    | _ -> None
  in
  let decls =
    List.map
      (fun (id, ty) ->
        Sasgn
          ( id,
            Some Tauto,
            CPPfun_call
              ( CPPmk_shared
                  (fix_func_type
                     (convert_ml_type_to_cpp_type env Refset'.empty tvars ty)),
                [] ) ) )
      renamed_ids
  in
  let defs =
    List.map2
      (fun (id, _fty) (args, body) ->
        Sderef_asgn
          ( CPPvar id,
            CPPlambda
              ( List.map
                  (fun (id, ty) ->
                    ( convert_ml_type_to_cpp_type env Refset'.empty tvars ty,
                      Some id ) )
                  args,
                ret_ty _fty,
                deref_subst body,
                true ) ) )
      renamed_ids funs_with_params
  in
  (decls, defs, deref_subst)

(** Generate local fixpoint declarations using the Y-combinator pattern
    for escaping fixpoints.

    Replaces the [shared_ptr<std::function>] pattern with a generic-lambda
    self-passing pattern:
    {v
      auto go_impl = [=](auto &_self, A... args) mutable -> R {
        ... _self(_self, args) ...
      };
      auto go = [=](A... args) mutable -> R {
        return go_impl(go_impl, args...);
      };
    v}

    No heap allocation, no [std::function] type erasure.  The [auto &_self]
    parameter uses C++14 generic lambdas.

    For mutual recursion with N functions, each impl takes N self parameters:
    {v
      auto f_impl = [=](auto &_sf, auto &_sg, A...) { ... _sg(_sf, _sg, ...) ... };
      auto g_impl = [=](auto &_sf, auto &_sg, A...) { ... _sf(_sf, _sg, ...) ... };
      auto f = [=](A...) { return f_impl(f_impl, g_impl, ...); };
      auto g = [=](A...) { return g_impl(f_impl, g_impl, ...); };
    v}

    @return [(decls, defs, deref_subst)] where [defs] is empty and
    [deref_subst] is the identity function (no dereferencing needed).
    @see gen_local_fix_by_ref for the non-escaping alternative. *)
and gen_local_fix_ycomb env renamed_ids funs_with_params =
  let tvars = get_current_type_vars () in
  let ret_ty ty =
    match convert_ml_type_to_cpp_type env Refset'.empty tvars ty with
    | Tfun (_, t) ->
      ( match t with
      | Minicpp.Tvar (_, None) -> None
      | _ -> Some t )
    | _ -> None
  in
  (* Create self-parameter IDs and impl IDs for each fixpoint. *)
  let self_ids =
    List.map
      (fun (id, _) -> Id.of_string ("_self_" ^ Id.to_string id))
      renamed_ids
  in
  let impl_ids =
    List.map
      (fun (id, _) -> Id.of_string (Id.to_string id ^ "_impl"))
      renamed_ids
  in
  (* The self-parameter CPP vars, in reversed order for prepending to
     reversed arg lists in CPPfun_call nodes. *)
  let self_vars_rev = List.rev_map (fun id -> CPPvar id) self_ids in
  (* Rewrite recursive calls in a body: for each fix_id, replace
     CPPfun_call(CPPvar fix_id, args) with
     CPPfun_call(CPPvar self_id, args @ self_vars_rev). *)
  let find_self_id id =
    let rec aux ids sids =
      match (ids, sids) with
      | (fix_id, _) :: _, sid :: _ when Id.equal id fix_id -> Some sid
      | _ :: ids', _ :: sids' -> aux ids' sids'
      | _ -> None
    in
    aux renamed_ids self_ids
  in
  let rec rewrite_expr e =
    match e with
    | CPPfun_call (CPPvar id, args) -> (
      match find_self_id id with
      | Some self_id ->
        CPPfun_call
          (CPPvar self_id, List.map rewrite_expr args @ self_vars_rev)
      | None -> CPPfun_call (CPPvar id, List.map rewrite_expr args) )
    | _ -> map_expr rewrite_expr rewrite_stmt Fun.id e
  and rewrite_stmt s = map_stmt rewrite_expr rewrite_stmt Fun.id s in
  (* Generate impl lambdas: each takes all self params (auto &) + original params. *)
  let impl_stmts =
    List.map2
      (fun ((_fix_id, fty), impl_id) (args, body) ->
        let self_params =
          List.rev_map (fun sid -> (Tref Tauto, Some sid)) self_ids
        in
        let orig_params =
          List.map
            (fun (id, ty) ->
              (convert_ml_type_to_cpp_type env Refset'.empty tvars ty, Some id))
            args
        in
        Sasgn
          ( impl_id,
            Some Tauto,
            CPPlambda
              ( orig_params @ self_params,
                ret_ty fty,
                List.map rewrite_stmt body,
                true ) ))
      (List.combine renamed_ids impl_ids)
      funs_with_params
  in
  (* Generate wrapper lambdas: forward to impl with all impl_ids prepended. *)
  let impl_vars_rev = List.rev_map (fun id -> CPPvar id) impl_ids in
  let wrapper_stmts =
    List.map2
      (fun ((fix_id, fty), impl_id) (args, _body) ->
        let orig_params =
          List.map
            (fun (id, ty) ->
              (convert_ml_type_to_cpp_type env Refset'.empty tvars ty, Some id))
            args
        in
        let fwd_args =
          List.rev_map (fun (id, _) -> CPPvar id) args @ impl_vars_rev
        in
        let rty = ret_ty fty in
        let call = CPPfun_call (CPPvar impl_id, fwd_args) in
        let wrapper_body =
          match rty with
          | None -> [Sexpr call]
          | _ -> [Sreturn (Some call)]
        in
        Sasgn
          ( fix_id,
            Some Tauto,
            CPPlambda (orig_params, rty, wrapper_body, true) ))
      (List.combine renamed_ids impl_ids)
      funs_with_params
  in
  let deref_subst stmts = stmts in
  (impl_stmts @ wrapper_stmts, [], deref_subst)

(** Generate C++ statements from an ML AST. The continuation [k] transforms the
    final expression into a statement (e.g., return, assignment). Handles
    let-bindings, pattern matching, fix expressions, and monadic operations. *)
and gen_stmts env (k : cpp_expr -> cpp_stmt) ast =
  match ast with
  | MLletin (_, _, MLfix (x, ids, funs, _), b) as _whole ->
    (* Special case for let-fix: the let binding name is the fix function name *)
    (* Resolve unresolved metas in fix function types to Tvars using mgu. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    (* Collect all Tvar indices from the fixpoint types *)
    let fix_tvar_indices =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
    in
    let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    (* Check if fixpoint introduces Tvars beyond the outer scope *)
    let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
    if has_extra_tvars then (
      (* Lift the polymorphic inner fixpoint to a top-level function. Build tvar
         names for all Tvars used in the fixpoint type: - Tvars 1..n_outer reuse
         the outer function's template param names - Tvars beyond n_outer get
         fresh names T<i> *)
      let all_tvar_names = build_tvar_names ~outer_tvars fix_tvar_indices in
      let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
      (* Generate the lifted function name *)
      let fix_name = fst ids.(x) in
      let outer_name =
        match tctx.current_outer_function_name with
        | Some n -> n
        | None -> "anon"
      in
      let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
      let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
      (* Save and set current_type_vars to the full tvar list for the lifted
         function *)
      let saved_tvars = get_current_type_vars () in
      set_current_type_vars all_tvar_names;
      (* Generate the fixpoint body using gen_fix, passing all mutual fixpoint
         names *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      (* Restore outer type vars *)
      set_current_type_vars saved_tvars;
      (* Build a lifted Dfundef for each fixpoint function (usually just one) *)
      let n_fix = Array.length funs in
      List.iteri
        (fun i ((renamed_id, fix_ty), params, body) ->
          let cpp_ty =
            convert_ml_type_to_cpp_type env Refset'.empty all_tvar_names fix_ty
          in
          let _, cod =
            match cpp_ty with
            | Tfun (dom, cod) -> (dom, cod)
            | _ -> ([], cpp_ty)
          in
          (* Detect params that are not simply forwarded at recursive call
             sites — these must keep std::function type to avoid infinite
             recursive template instantiation. *)
          let non_fwd_source_indices =
            let lam_params, stripped_body =
              Mlutil.collect_lams funs.(i)
            in
            detect_non_forwarded_params_fix
              (List.length lam_params) n_fix i stripped_body
          in
          let cpp_params, all_temps_with_funs =
            build_lifted_cpp_params
              ~non_fwd_source_indices
              (convert_ml_type_to_cpp_type env Refset'.empty all_tvar_names)
              all_temps
              params
          in
          (* Replace recursive self-references (CPPvar renamed_n) with calls to
             the lifted function *)
          let rec_call =
            mk_cppglob
              lifted_ref
              (List.map (fun id -> Tvar (0, Some id)) all_tvar_names)
          in
          let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
          let inner = Dfundef ([(lifted_ref, [])], cod, cpp_params, body, false) in
          let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
          add_lifted_decl lifted_decl )
        funs_compiled;
      (* In the continuation body b, the fixpoint name should resolve to a call
         to the lifted function with appropriate type arguments. We push the fix
         name into the env so that MLrel references in b resolve correctly. *)
      let projected_fix_id = (fst ids.(x), snd ids.(x)) in
      let _, env_with_fix = push_vars' [projected_fix_id] env in
      push_env_types [projected_fix_id];
      (* Generate b, then replace references to the fixpoint var with calls to
         the lifted function. Build explicit type args: outer tvars stay as Tvar
         references, extra tvars are resolved to concrete types from the
         enclosing function's return type. *)
      let call_type_args =
        let extra_tvar_names =
          List.filter
            (fun id -> not (List.exists (Id.equal id) outer_tvars))
            all_tvar_names
        in
        if extra_tvar_names = [] then
          List.map (fun id -> Tvar (0, Some id)) outer_tvars
        else
          let fix_ty = snd ids.(0) in
          let tmpl_cpp_ty =
            convert_ml_type_to_cpp_type env Refset'.empty all_tvar_names fix_ty
          in
          let tmpl_cod =
            match tmpl_cpp_ty with
            | Tfun (_, cod) -> cod
            | t -> t
          in
          let outer_args = List.map (fun id -> Tvar (0, Some id)) outer_tvars in
          let extra_args =
            List.map
              (fun tvar_name ->
                match tmpl_cod with
                | Tvar (_, Some id) when Id.equal id tvar_name ->
                  ( match tctx.current_cpp_return_type with
                  | Some ret_ty -> ret_ty
                  | None -> Tvar (0, Some tvar_name) )
                | _ ->
                match tctx.current_cpp_return_type with
                | Some ret_ty -> ret_ty
                | None -> Tvar (0, Some tvar_name) )
              extra_tvar_names
          in
          outer_args @ extra_args
      in
      let lifted_call = mk_cppglob lifted_ref call_type_args in
      (* Phase 2: shift owned vars for the single let binding *)
      let saved_owned_lifted = tctx.move_owned_vars in
      tctx.move_owned_vars <-
        Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
      let result = gen_stmts env_with_fix k b in
      tctx.move_owned_vars <- saved_owned_lifted;
      List.map (local_var_subst_stmt fix_name lifted_call) result )
    else
      (* No extra Tvars — proceed with local fixpoint approach.

         Three sub-steps:
         1. Compile all mutual fixpoint bodies via {!gen_fix}.
         2. Push only the PROJECTED fixpoint (the one this [MLletin]
            binds) into the continuation environment — not all mutual
            fix names, which would shift de Bruijn indices by [n]
            instead of the correct [1].
         3. Run escape analysis ({!fixpoint_escapes_in_stmts}) on the
            compiled continuation to decide between the [\[&\]] pattern
            ({!gen_local_fix_by_ref}) and the [shared_ptr] pattern
            ({!gen_local_fix_shared_ptr}).

         Move tracking: variables captured by the fixpoint bodies
         ({!Escape.free_rels}) are removed from [move_owned_vars] so
         that [dead_in_a] does not [std::move] them while the fixpoint's
         [\[&\]] lambda still holds references ([fix_move_capture]). *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      let renamed_ids =
        List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
      in
      let funs_with_params =
        List.map (fun (_, params, body) -> (params, body)) funs_compiled
      in
      (* Add only the PROJECTED fixpoint id to the continuation env.
         MLletin binds ONE variable (the projected fixpoint), not all mutual
         fix functions.  Pushing all fix names would shift de Bruijn indices
         by n instead of 1, corrupting references in the continuation.
         However, ALL fix names are added to the avoid set to prevent
         name clashes in subsequent fixpoints (e.g., when the same mutual
         block is instantiated again with a different projection). *)
      let projected_id = List.nth renamed_ids x in
      (* Add non-projected fix names to the avoid set so that subsequent
         fixpoints (e.g., a second MLfix with a different projection from
         the same mutual block) will rename conflicting names. *)
      let env_for_cont =
        let (db, avoid) = env in
        let avoid' = List.fold_left
          (fun acc (i, (id, _)) ->
            if i <> x then Id.Set.add id acc else acc)
          avoid (List.mapi (fun i x -> (i, x)) renamed_ids)
        in
        (db, avoid')
      in
      let _, env_with_fix = push_vars' [projected_id] env_for_cont in
      push_env_types [projected_id];
      (* Compute outer variables captured by the fixpoint bodies.
         If the fixpoint ends up using [&] capture, these variables must
         not be moved in the continuation — the fixpoint holds references
         to them. Even if the fixpoint later uses [=] (escape path),
         suppressing moves is safe (just conservative: copies instead
         of moves for those vars). *)
      let fix_captured =
        Array.fold_left
          (fun acc body ->
            Escape.IntSet.union acc
              (Escape.free_rels (Array.length ids) body))
          Escape.IntSet.empty funs
      in
      (* Shift captured indices: free var at index i in the fix scope
         becomes i+1 in the continuation (one let-binding added). *)
      let captured_shifted =
        Escape.IntSet.map (fun i -> i + 1) fix_captured
      in
      (* Phase 2: shift owned vars and dead-after for the single let binding.
         Remove captured variables from owned set to prevent moves. *)
      let saved_owned = tctx.move_owned_vars in
      let saved_dead_fix = tctx.move_dead_after in
      tctx.move_owned_vars <-
        Escape.IntSet.diff
          (Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars)
          captured_shifted;
      tctx.move_dead_after <-
        Escape.IntSet.map (fun i -> i + 1) tctx.move_dead_after;
      let cont = gen_stmts env_with_fix k b in
      tctx.move_owned_vars <- saved_owned;
      tctx.move_dead_after <- saved_dead_fix;
      (* Check if any fixpoint variable escapes in the continuation.
         If so, use shared_ptr + [=] to prevent dangling references.
         Otherwise, use the simpler [&] capture pattern. *)
      let any_escapes =
        List.exists
          (fun (id, _) -> fixpoint_escapes_in_stmts id cont)
          renamed_ids
      in
      if any_escapes then
        let decls, defs, deref_subst =
          gen_local_fix_ycomb env renamed_ids funs_with_params
        in
        decls @ defs @ deref_subst cont
      else
        let decls, defs =
          gen_local_fix_by_ref env renamed_ids funs_with_params
        in
        decls @ defs @ cont
  | MLletin (x, t, (MLlam _ as a), b) ->
    (* Check if this is a polymorphic lambda that should be lifted to a
       top-level template function. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    resolve_metas t;
    resolve_metas_in_ast resolve_metas a;
    (* Collect all Tvar indices from the let-binding type *)
    let tvar_indices = collect_tvars [] t in
    (* Also collect Tvars from the lambda body *)
    let body_tvars = collect_tvars_ast [] a in
    let all_body_tvars = List.sort_uniq Int.compare body_tvars in
    let tvar_indices = List.sort Int.compare tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    let has_extra = List.exists (fun i -> i > n_outer) tvar_indices in
    (* Normal MLletin fallback (shared by no-extra-tvars and
       thunk-with-free-vars cases) *)
    let gen_normal_letin () =
      let x' = remove_prime_id (id_of_mlid x) in
      let renamed_ids, env' = push_vars' [(x', t)] env in
      let x_renamed = fst (List.hd renamed_ids) in
      if x == Dummy then (
        push_env_types [(x_renamed, t)];
        gen_stmts env' k b )
      else if tctx.itree_mode = Reified && is_monadic_ml_type t then begin
        (* Monadic let-binding (reified mode): wrap RHS in an ITree IIFE so
           the variable has type [shared_ptr<ITree<R>>]. *)
        Table.require_itree_header ();
        push_env_types [(x_renamed, t)];
        let tvars = get_current_type_vars () in
        let r_ml = extract_itree_result_ml t in
        let r_cpp = convert_ml_type_to_cpp_type env Refset'.empty tvars r_ml in
        (* Voidify unit result type in ITree wrapper *)
        let r_cpp = if ml_type_is_unit r_ml then Tvoid else r_cpp in
        let reified_ty = mk_itree_type r_cpp in
        let ret_k v = Sreturn (Some (mk_itree_ret_for_value r_cpp r_ml v)) in
        let body_stmts = gen_stmts env ret_k a in
        let iife = CPPfun_call (
          CPPlambda ([], Some reified_ty, body_stmts, false), []) in
        (* Shift owned vars and dead-after for the continuation *)
        let saved_owned_lam = tctx.move_owned_vars in
        let saved_dead_lam = tctx.move_dead_after in
        tctx.move_owned_vars <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
        tctx.move_dead_after <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_dead_after;
        let cont = gen_stmts env' k b in
        tctx.move_owned_vars <- saved_owned_lam;
        tctx.move_dead_after <- saved_dead_lam;
        (* Generate the assignment with reified type *)
        [Sasgn (x_renamed, Some reified_ty, iife)] @ cont
      end else
        let afun v = Sasgn (x_renamed, None, v) in
        let asgn = gen_stmts env afun a in
        (* Push env_types AFTER generating the value expression [a]. *)
        push_env_types [(x_renamed, t)];
        let tvars = get_current_type_vars () in
        (* Phase 2: shift owned vars and dead-after for lambda let binding.
           The body [b] has one more de Bruijn binder, so all indices must
           be shifted +1. *)
        let saved_owned_lam = tctx.move_owned_vars in
        let saved_dead_lam = tctx.move_dead_after in
        tctx.move_owned_vars <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
        tctx.move_dead_after <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_dead_after;
        let gen_cont () =
          let cont = gen_stmts env' k b in
          tctx.move_owned_vars <- saved_owned_lam;
          tctx.move_dead_after <- saved_dead_lam;
          cont
        in
        match asgn with
        | [Sasgn (_, None, e)] ->
          Sasgn
            ( x_renamed,
              Some (convert_ml_type_to_cpp_type env Refset'.empty tvars t),
              e )
          :: gen_cont ()
        | _ ->
          Sdecl
            (x_renamed, convert_ml_type_to_cpp_type env Refset'.empty tvars t)
          :: asgn
          @ gen_cont ()
    in
    if not has_extra then
      gen_normal_letin ()
    else (* Lift the polymorphic lambda to a top-level template function. *)
      let params, body = collect_lams a in
      let n_params = List.length params in
      let x' = remove_prime_id (id_of_mlid x) in

      (* 1. Collect free variables in the lambda body *)
      let free_indices = collect_free_rels n_params body in
      let free_vars =
        List.map
          (fun i ->
            let name = get_db_name i env in
            let ty = get_env_type i in
            (name, ty, i) )
          (List.sort Int.compare free_indices)
      in

      (* Check if all parameters are dummy/void - if so, this is likely a thunk
         for monadic ops *)
      let all_params_dummy =
        List.for_all (fun (_, ty) -> isTdummy ty || ml_type_is_void ty) params
      in

      if all_params_dummy then
        (* All lambda params are erased type params — this is a polymorphic
           function alias like `let alias := @id`. Don't lift to a top-level
           template; instead inline the lambda into the continuation and
           beta-reduce, so that call sites like `alias nat 9` become direct
           calls like `id(9)`. *)
        let b' = ast_subst a b in
        let rec beta_red_app args = function
          | MLlam (_, _, body) ->
            ( match args with
            | [] -> MLlam (Dummy, Tdummy Ktype, beta_normalize body)
            | _ :: rest -> beta_red_app rest (ast_pop body) )
          | f ->
            let f = beta_normalize f in
            if args = [] then
              f
            else
              MLapp (f, List.map beta_normalize args)
        and beta_normalize = function
          | MLapp ((MLlam _ as f), args) -> beta_red_app args f
          | t -> ast_map beta_normalize t
        in
        let b' = beta_normalize b' in
        gen_stmts env k b'
      else
        (* 2. Build tvar names: outer tvars keep their names, extra tvars get
           fresh names *)
        let all_tvar_names = build_tvar_names ~outer_tvars tvar_indices in
        let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in

        let extended_tvar_names =
          build_extended_tvar_names tvar_indices all_tvar_names all_body_tvars
        in

        (* 3. Generate the lifted function name *)
        let outer_name =
          match tctx.current_outer_function_name with
          | Some n -> n
          | None -> "anon"
        in
        let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string x' in
        let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in

        (* 4. Substitution helper for call sites: replace CPPfun_call(CPPvar x',
           args) with CPPfun_call(CPPglob(lifted_ref, []), free_var_cpps @
           args) *)
        let rec subst_lifted_call_expr
            (target : Id.t)
            (lifted : GlobRef.t)
            (free_args : cpp_expr list)
            (e : cpp_expr) =
          let sub = subst_lifted_call_expr target lifted free_args in
          match e with
          | CPPfun_call (CPPvar id, args) when Id.equal id target ->
            CPPfun_call (mk_cppglob lifted [], free_args @ List.map sub args)
          | CPPvar id when Id.equal id target ->
            (* Bare reference to lifted function: if there are free args, wrap
               in a lambda *)
            if free_args = [] then
              mk_cppglob lifted []
            else
              (* Generate a lambda that captures and forwards: [&]() { return
                 lifted(free_args...); } *)
              CPPlambda
                ( [],
                  None,
                  [
                    Sreturn
                      (Some (CPPfun_call (mk_cppglob lifted [], free_args)));
                  ],
                  false )
          | CPPfun_call (f, args) -> CPPfun_call (sub f, List.map sub args)
          | CPPderef e' -> CPPderef (sub e')
          | CPPmove e' -> CPPmove (sub e')
          | CPPlambda (args, ty, b, cbv) ->
            CPPlambda
              ( args,
                ty,
                List.map (subst_lifted_call_stmt target lifted free_args) b,
                cbv )
          | CPPoverloaded cases -> CPPoverloaded (List.map sub cases)
          | CPPstructmk (id', tys, args) ->
            CPPstructmk (id', tys, List.map sub args)
          | CPPstruct (id', tys, args) -> CPPstruct (id', tys, List.map sub args)
          | CPPget (e', id') -> CPPget (sub e', id')
          | CPPget' (e', id') -> CPPget' (sub e', id')
          | CPPnamespace (id', e') -> CPPnamespace (id', sub e')
          | CPPparray (args, e') -> CPPparray (Array.map sub args, sub e')
          | CPPmethod_call (obj, meth, args) ->
            CPPmethod_call (sub obj, meth, List.map sub args)
          | CPPmember (e', mid) -> CPPmember (sub e', mid)
          | CPParrow (e', mid) -> CPParrow (sub e', mid)
          | CPPforward (ty, e') -> CPPforward (ty, sub e')
          | CPPnew (ty, args) -> CPPnew (ty, List.map sub args)
          | CPPshared_ptr_ctor (ty, e') -> CPPshared_ptr_ctor (ty, sub e')
          | CPPstruct_id (sid, tys, args) ->
            CPPstruct_id (sid, tys, List.map sub args)
          | CPPqualified (e', qid) -> CPPqualified (sub e', qid)
          | CPPany_cast (_, CPPfun_call (CPPvar id, args)) when Id.equal id target ->
            (* The any_cast wraps a direct call to the variable being lifted.
               The lifted template function returns a concrete type (not
               std::any), so drop the cast and replace with the lifted call. *)
            CPPfun_call (mk_cppglob lifted [], free_args @ List.map sub args)
          | CPPany_cast (ty, e') -> CPPany_cast (ty, sub e')
          | _ -> e
        and subst_lifted_call_stmt
            (target : Id.t)
            (lifted : GlobRef.t)
            (free_args : cpp_expr list)
            (s : cpp_stmt) =
          match s with
          | Sreturn (Some e) ->
            Sreturn (Some (subst_lifted_call_expr target lifted free_args e))
          | Sreturn None -> Sreturn None
          | Sasgn (id, ty, e) ->
            Sasgn (id, ty, subst_lifted_call_expr target lifted free_args e)
          | Sexpr e -> Sexpr (subst_lifted_call_expr target lifted free_args e)
          | Scustom_case (ty, e, tys, brs, str) ->
            Scustom_case
              ( ty,
                subst_lifted_call_expr target lifted free_args e,
                tys,
                List.map
                  (fun (args, ty, stmts) ->
                    ( args,
                      ty,
                      List.map
                        (subst_lifted_call_stmt target lifted free_args)
                        stmts ) )
                  brs,
                str )
          | _ -> s
        in

        (* 6. Compile the lambda body with extended type variables *)
        let saved_tvars = get_current_type_vars () in
        set_current_type_vars extended_tvar_names;
        (* Push lambda params into env for body compilation *)
        let param_ids =
          List.map
            (fun (ml_id, ty) -> (remove_prime_id (id_of_mlid ml_id), ty))
            params
        in
        (* For free variables, we need to adjust de Bruijn indices in the body.
           The body references free vars as MLrel (n_params + i) where i is the
           outer index. We compile with an env that has: [free_var_params...;
           lambda_params...] So we push free var names first, then lambda param
           names. *)
        let free_var_params =
          List.map (fun (name, ty, _) -> (name, ty)) free_vars
        in
        let body_params_for_env = free_var_params @ param_ids in
        let body_param_ids, body_env = push_vars' body_params_for_env env in
        let saved_env_types = tctx.env_types in
        push_env_types body_param_ids;

        (* Now compile the body. The body's de Bruijn indices: MLrel 1..n_params
           -> lambda params (at positions n_free+1..n_free+n_params in our env)
           MLrel n_params+i -> free var i (should map to position n_free-i+1 in
           our env, but we actually need to adjust: MLrel (n_params +
           orig_outer_idx) in the body maps to outer env position
           orig_outer_idx. In our extended env, free vars are at positions
           n_params+1..n_params+n_free. So we need to remap. Actually, the body
           already has correct de Bruijn indices: - MLrel 1..n_params are the
           lambda params - MLrel (n_params + i) references outer scope position
           i When we push [free_var_params @ param_ids], the env has: positions
           1..n_params = param_ids (lambda params) positions
           n_params+1..n_params+n_free = free_var_params But the body references
           MLrel(n_params + original_outer_idx), and original_outer_idx may not
           equal the position in free_var_params. We need the body env to map
           MLrel(n_params + i) correctly for each free var. *)

        (* Simpler approach: compile body in a modified env where free vars at
           their original positions are accessible. We push only the lambda
           params on top of the outer env. *)
        let lam_param_ids, lam_env = push_vars' param_ids env in
        tctx.env_types <- saved_env_types;
        push_env_types lam_param_ids;
        (* Lambda bodies have their own return type; clear the enclosing
           function's void flag to avoid bare 'return;' inside the lambda. *)
        let saved_return_type = tctx.current_cpp_return_type in
        ( if tctx.current_cpp_return_type = Some Tvoid then
            tctx.current_cpp_return_type <- None );
        let compiled_body =
          gen_stmts lam_env (fun x -> Sreturn (Some x)) body
        in
        tctx.current_cpp_return_type <- saved_return_type;
        tctx.env_types <- saved_env_types;
        set_current_type_vars saved_tvars;

        (* 7. Now substitute free variable references in compiled body: Free
           vars in the body were compiled as CPPvar(name_from_outer_env). In the
           lifted function, they become parameters. The names are the same, so
           no substitution of the body is needed — the free var params have the
           same names as the outer scope variables. *)

        (* 8. Build the lifted function parameters: free vars first, then lambda
           params *)
        let all_lifted_params =
          free_var_params
          @ List.filter
              (fun (_, ty) -> (not (ml_type_is_void ty)) && not (isTdummy ty))
              lam_param_ids
        in
        let cpp_params, all_temps_with_funs =
          build_lifted_cpp_params
            (convert_ml_type_to_cpp_type
               lam_env
               Refset'.empty
               extended_tvar_names )
            all_temps
            all_lifted_params
        in

        (* Get return type from the let-binding type *)
        let cpp_ty =
          convert_ml_type_to_cpp_type
            lam_env
            Refset'.empty
            extended_tvar_names
            t
        in
        let cod =
          match cpp_ty with
          | Tfun (_, cod) -> cod
          | _ -> cpp_ty
        in

        (* 9. Build and register the lifted declaration *)
        let inner =
          Dfundef ([(lifted_ref, [])], cod, cpp_params, compiled_body, false)
        in
        let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
        add_lifted_decl lifted_decl;

        (* 10. Compile the continuation body b, substituting calls to x' with
           calls to the lifted function *)
        let lifted_ids, env' = push_vars' [(x', t)] env in
        let x_lifted = fst (List.hd lifted_ids) in
        push_env_types [(x_lifted, t)];
        (* Phase 2: shift owned vars for lifted lambda binding *)
        let saved_owned_lifted2 = tctx.move_owned_vars in
        tctx.move_owned_vars <-
          Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars;
        let cont = gen_stmts env' k b in
        tctx.move_owned_vars <- saved_owned_lifted2;
        (* Build the free variable argument expressions *)
        let free_var_cpps =
          List.map (fun (name, _, _) -> CPPvar name) free_vars
        in
        List.map
          (subst_lifted_call_stmt x_lifted lifted_ref free_var_cpps)
          cont
  | MLletin (x, t, a, b) ->
    let x' = remove_prime_id (id_of_mlid x) in
    let ids_renamed, env' = push_vars' [(x', t)] env in
    let x_renamed = fst (List.hd ids_renamed) in
    if x == Dummy then (
      push_env_types [(x_renamed, t)];
      with_shifted_move_tracking 1 (fun () ->
        gen_stmts env' k b) )
    else if ml_type_is_unit t then (
      (* Unit-typed let bindings: the RHS may call a void-ified function,
         so we can't assign its result to a variable.  Execute the RHS for
         side effects, then declare the variable as Unit::e_TT (its only
         possible value) so the body can still reference it. *)
      push_env_types [(x_renamed, t)];
      let rhs = gen_stmts env (fun e -> Sexpr e) a in
      (* Drop trivially pure RHS (e.g. Unit::e_TT from tt, variable refs) *)
      let rhs = List.filter (fun s ->
        match s with
        | Sexpr (CPPenum_val _) -> false
        | Sexpr (CPPvar _) -> false
        | _ -> true) rhs in
      (* Generate the body first (under shifted move tracking for the new
         binder), then check if the variable is actually referenced in the
         generated C++ (not just the ML AST, since optimizations like
         unit-match elimination may drop references). *)
      let body =
        with_shifted_move_tracking 1 (fun () -> gen_stmts env' k b)
      in
      let decl =
        if stmts_reference_var x_renamed body then
          let tvars = get_current_type_vars () in
          let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars t in
          [Sasgn (x_renamed, Some cpp_ty, mk_tt_expr ())]
        else []
      in
      rhs @ decl @ body )
    else
      let depth = tctx.current_letin_depth in
      tctx.current_letin_depth <- depth + 1;
      (* Phase 2: set up dead-after info for move insertion. Compute free vars
         of the continuation [b] (shifted by 1 because [b] is under the let
         binder). A variable at de Bruijn index [i] in [a] is dead-after if
         [i+1] is not free in [b] (since [b] has one extra binder). Only move if
         the variable has exactly 1 occurrence in [a]. *)
      let saved_dead = tctx.move_dead_after in
      let saved_owned = tctx.move_owned_vars in
      let cont_free = Escape.free_rels 1 b in
      (* free in b, shifted past let binder *)
      let dead_in_a =
        Escape.IntSet.filter
          (fun i ->
            (* i is dead after [a] if i is not free in [b] AND occurs exactly
               once in [a] *)
            (not (Escape.IntSet.mem i cont_free))
            && Escape.nb_occur_match i a = 1 )
          tctx.move_owned_vars
      in
      (* Also add any vars from our current dead set that have single occurrence
         in a *)
      let dead_from_above =
        Escape.IntSet.filter
          (fun i ->
            Escape.IntSet.mem i tctx.move_dead_after
            && Escape.nb_occur_match i a = 1 )
          tctx.move_owned_vars
      in
      tctx.move_dead_after <- Escape.IntSet.union dead_in_a dead_from_above;
      let saved_suppress = tctx.move_suppress_tail in
      tctx.move_suppress_tail <- true;
      (* Single-use partial application optimization: when the RHS is a partial
         application and the bound variable is used at most once in the
         continuation without escaping, AND all free variables of the RHS are
         dead in the continuation (so [&] capture references stay valid),
         tell eta_fun to keep CPPmove wrappers and use [&] capture for
         zero-copy closure generation. *)
      let is_single_use_partial_app =
        match a with
        | MLapp (head, ml_args) | MLmagic (MLapp (head, ml_args)) ->
          (match Escape.partial_app_remaining head ml_args with
           | Some remaining ->
             Escape.nb_occur_match 1 b <= 1
             && not (Escape.escapes 1 b)
             && Escape.IntSet.is_empty
                  (Escape.IntSet.inter (Escape.free_rels 0 a) cont_free)
             && Escape.single_use_nargs 1 b >= remaining
           | None -> false)
        | _ -> false
      in
      let saved_eta_keep = tctx.eta_keep_moves in
      if is_single_use_partial_app then tctx.eta_keep_moves <- true;
      let afun v = Sasgn (x_renamed, None, v) in
      let asgn = gen_stmts env afun a in
      tctx.eta_keep_moves <- saved_eta_keep;
      (* Push env_types AFTER generating the value expression [a] — [a] uses de
         Bruijn indices that don't include the new let binding.  The body [b]
         (generated below) does include it. *)
      push_env_types [(x_renamed, t)];
      tctx.move_suppress_tail <- saved_suppress;
      (* Shift saved_dead +1 for the body [b]: the new let binding adds one
         de Bruijn level, so all parent-scope indices must be shifted to stay
         in sync with the body's coordinate system. *)
      tctx.move_dead_after <- Escape.IntSet.map (fun i -> i + 1) saved_dead;
      (* The new let binding is owned (it's a local variable). Update
         move_owned_vars for processing [b]: shift all existing indices by 1
         (because [b] has one more binder) and add index 1 if the type is
         shared_ptr. *)
      let shifted_owned =
        Escape.IntSet.map (fun i -> i + 1) tctx.move_owned_vars
      in
      (* Const-ref binding optimisation: when the RHS [a] is a record-field
         access (single-branch MLcase) on a BORROWED source variable — i.e., a
         variable that is not in [move_owned_vars] (passed by const ref, not
         owned) — we can bind the result as [const T&] instead of [T].  This
         avoids an unnecessary shared_ptr refcount increment at the binding
         site; any subsequent owned uses still copy from the reference.

         The source is borrowed iff its de Bruijn index is NOT in the current
         (pre-shift) [move_owned_vars].  We only apply this when the type is a
         shared_ptr so that primitive types (int, bool) are left unchanged. *)
      let use_const_ref =
        Escape.is_shared_ptr_type t
        &&
        ( match a with
          | MLcase (_, MLrel k, pv)
            when Array.length pv = 1
                 && (match pv.(0) with (_, _, _, MLrel _) -> true | _ -> false)
                 && not (Escape.IntSet.mem k tctx.move_owned_vars) ->
            true
          | _ -> false )
      in
      let new_is_shared = Escape.is_shared_ptr_type t && not use_const_ref in
      let owned_for_b =
        if new_is_shared then
          Escape.IntSet.add 1 shifted_owned
        else
          shifted_owned
      in
      tctx.move_owned_vars <- owned_for_b;
      let tvars = get_current_type_vars () in
      let result =
        match asgn with
          | [Sasgn (_, None, e)] ->
            let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars t in
            (* When the type contains Tany (from erased carrier projections) but
               the generated expression is a lambda with concrete types, derive
               the std::function type from the lambda's parameter and return
               types. *)
            let cpp_ty =
              match (cpp_ty, e) with
              | Tfun (_, _), CPPlambda (params, Some ret_ty, _, _)
                when has_tany_in_type cpp_ty ->
                let strip_tmod = function
                  | Tmod (_, t) -> t
                  | t -> t
                in
                let param_tys =
                  List.rev_map (fun (ty, _) -> strip_tmod ty) params
                in
                Tfun (param_tys, ret_ty)
              | _ -> cpp_ty
            in
            (* Apply const-ref binding when safe. *)
            let cpp_ty =
              if use_const_ref then Tref (Tmod (TMconst, cpp_ty))
              else cpp_ty
            in
            begin match extract_block_template e with
            | Some (ref, tmpl, args, tys) ->
              Sblock_custom (ref, tmpl, x_renamed, cpp_ty, args, tys)
              :: gen_stmts env' k b
            | None ->
              Sasgn (x_renamed, Some cpp_ty, e) :: gen_stmts env' k b
            end
          | _ ->
            let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars t in
            (Sdecl (x_renamed, cpp_ty) :: asgn) @ gen_stmts env' k b
      in
      tctx.move_owned_vars <- saved_owned;
      result
  | MLapp (MLfix (x, ids, funs, _), args) ->
    (* Resolve unresolved metas in fix function types to Tvars using mgu.
       Traverse types and assign Tvar 1, 2, ... to each unresolved meta. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    Array.iter (resolve_metas_in_ast resolve_metas) funs;
    List.iter (resolve_metas_in_ast resolve_metas) args;
    (* Collect Tvars from bodies too *)
    let body_tvars = Array.fold_left collect_tvars_ast [] funs in
    let all_body_tvars = List.sort_uniq Int.compare body_tvars in
    (* Collect all Tvar indices from the fixpoint types *)
    let fix_tvar_indices =
      Array.fold_left (fun acc (_, ty) -> collect_tvars acc ty) [] ids
    in
    let fix_tvar_indices = List.sort Int.compare fix_tvar_indices in
    let outer_tvars = get_current_type_vars () in
    let n_outer = List.length outer_tvars in
    (* Check if fixpoint introduces Tvars beyond the outer scope *)
    let has_extra_tvars = List.exists (fun i -> i > n_outer) fix_tvar_indices in
    if has_extra_tvars then (
      (* Lift the polymorphic inner fixpoint to a top-level function *)
      let all_tvar_names = build_tvar_names ~outer_tvars fix_tvar_indices in
      let all_temps = List.map (fun id -> (TTtypename, id)) all_tvar_names in
      let extended_tvar_names =
        build_extended_tvar_names fix_tvar_indices all_tvar_names all_body_tvars
      in
      let fix_name = fst ids.(x) in
      let outer_name =
        match tctx.current_outer_function_name with
        | Some n -> n
        | None -> "anon"
      in
      let lifted_name_str = "_" ^ outer_name ^ "_" ^ Id.to_string fix_name in
      let lifted_ref = GlobRef.VarRef (Id.of_string lifted_name_str) in
      (* Save and set current_type_vars to the extended tvar list for the lifted
         function. extended_tvar_names covers both signature and body Tvar
         indices. *)
      let saved_tvars = get_current_type_vars () in
      set_current_type_vars extended_tvar_names;
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      set_current_type_vars saved_tvars;
      (* Build lifted declarations *)
      let n_fix = Array.length funs in
      List.iteri
        (fun i ((renamed_id, fix_ty), params, body) ->
          let cpp_ty =
            convert_ml_type_to_cpp_type
              env
              Refset'.empty
              extended_tvar_names
              fix_ty
          in
          let _, cod =
            match cpp_ty with
            | Tfun (dom, cod) -> (dom, cod)
            | _ -> ([], cpp_ty)
          in
          let non_fwd_source_indices =
            let lam_params, stripped_body =
              Mlutil.collect_lams funs.(i)
            in
            detect_non_forwarded_params_fix
              (List.length lam_params) n_fix i stripped_body
          in
          let cpp_params, all_temps_with_funs =
            build_lifted_cpp_params
              ~non_fwd_source_indices
              (convert_ml_type_to_cpp_type
                 env
                 Refset'.empty
                 extended_tvar_names )
              all_temps
              params
          in
          let rec_call =
            mk_cppglob
              lifted_ref
              (List.map (fun id -> Tvar (0, Some id)) all_tvar_names)
          in
          let body = List.map (local_var_subst_stmt renamed_id rec_call) body in
          let inner = Dfundef ([(lifted_ref, [])], cod, cpp_params, body, false) in
          let lifted_decl = Dtemplate (all_temps_with_funs, None, inner) in
          add_lifted_decl lifted_decl )
        funs_compiled;
      (* Generate args in outer scope and call the lifted function. Build
         explicit type args: outer tvars stay as Tvar references, extra tvars
         are resolved to concrete types from the enclosing context. Extra tvars
         that appear as the fixpoint's return type are resolved to the enclosing
         function's C++ return type (current_cpp_return_type). *)
      let call_type_args =
        let extra_tvar_names =
          List.filter
            (fun id -> not (List.exists (Id.equal id) outer_tvars))
            all_tvar_names
        in
        if extra_tvar_names = [] then
          (* All tvars are outer — C++ can deduce them *)
          []
        else
          (* Get the fixpoint's template return type to identify which extra
             tvar it uses *)
          let fix_ty = snd ids.(x) in
          let tmpl_cpp_ty =
            convert_ml_type_to_cpp_type
              env
              Refset'.empty
              extended_tvar_names
              fix_ty
          in
          let tmpl_cod =
            match tmpl_cpp_ty with
            | Tfun (_, cod) -> cod
            | t -> t
          in
          let outer_args = List.map (fun id -> Tvar (0, Some id)) outer_tvars in
          let extra_args =
            List.map
              (fun tvar_name ->
                (* If this extra tvar IS the template return type, use the
                   enclosing function's concrete return type as the
                   instantiation. *)
                match tmpl_cod with
                | Tvar (_, Some id) when Id.equal id tvar_name ->
                  ( match tctx.current_cpp_return_type with
                  | Some ret_ty -> ret_ty
                  | None -> Tvar (0, Some tvar_name) )
                | _ ->
                (* For non-return-type extra tvars, keep as Tvar — C++ may
                   deduce them from arguments, or further analysis is needed. *)
                match tctx.current_cpp_return_type with
                | Some ret_ty ->
                  ret_ty (* Best guess: use enclosing return type *)
                | None -> Tvar (0, Some tvar_name) )
              extra_tvar_names
          in
          outer_args @ extra_args
      in
      let cpp_args = List.rev_map (gen_expr env) args in
      [k (CPPfun_call (mk_cppglob lifted_ref call_type_args, cpp_args))] )
    else (* No extra Tvars - proceed with by-ref local fixpoint (immediately applied) *)
      let all_fix_ids_list = Array.to_list ids in
      let funs_compiled =
        Array.to_list
          (Array.mapi
             (fun i f ->
               gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
             funs )
      in
      let renamed_ids =
        List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
      in
      let funs_with_params =
        List.map (fun (_, params, body) -> (params, body)) funs_compiled
      in
      let decls, defs =
        gen_local_fix_by_ref env renamed_ids funs_with_params
      in
      let args = List.rev_map (gen_expr env) args in
      decls @ defs
      @ [k (CPPfun_call
              (CPPvar (fst (List.nth renamed_ids x)), args))]
  | MLfix (x, ids, funs, _) ->
    (* Standalone fixpoint (not immediately applied) — e.g., appearing as the
       RHS of a let-binding.  Since the fixpoint value itself is returned (not
       called in place), it will always escape.  Use the Y-combinator pattern:
       the generated wrapper lambda [fix_name] is already a plain callable. *)
    let next_tvar = ref 1 in
    let resolve_metas = resolve_type_metas ~next_tvar in
    Array.iter (fun (_, ty) -> resolve_metas ty) ids;
    let all_fix_ids_list = Array.to_list ids in
    let funs_compiled =
      Array.to_list
        (Array.mapi
           (fun i f ->
             gen_fix env ~all_fix_ids:all_fix_ids_list ~fix_idx:i ids.(i) f )
           funs )
    in
    let renamed_ids =
      List.map (fun (renamed_id, _, _) -> renamed_id) funs_compiled
    in
    let funs_with_params =
      List.map (fun (_, params, body) -> (params, body)) funs_compiled
    in
    let decls, defs, _deref_subst =
      gen_local_fix_ycomb env renamed_ids funs_with_params
    in
    let fix_id = fst (List.nth renamed_ids x) in
    decls @ defs @ [k (CPPvar fix_id)]
  (* | MLapp (MLglob (h, _), a1 :: a2 :: l) when is_hoist h -> gen_stmts env k
     (MLapp (a1, a2::[])) *)
  | MLapp (MLglob (r, bind_tys), a1 :: a2 :: l) when is_bind r ->
    (* Reified mode: bind is a real function call, not desugared. *)
    if tctx.itree_mode = Reified then
      let saved_dead = tctx.move_dead_after in
      let e = gen_tail_expr env ast in
      let result = inline_iife k e in
      tctx.move_dead_after <- saved_dead;
      result
    else begin
      (* Sequential mode: desugar bind into sequential statements. *)
      let a_ml, f = Common.last_two (a1 :: a2 :: l) in
      let a = gen_expr env a_ml in
      let ids', f = collect_lams f in
    (* Resolve metas in continuation parameter types using bind's type
       arguments. bind has type forall A B, IO A -> (A -> IO B) -> IO B. The
       first type argument is A, which is the type of the continuation
       parameter. Use mgu to unify them, which mutably resolves metas. Skip
       Tdummy entries in bind_tys — these come from failed type extractions in
       make_tyargs (e.g., HKT type constructors that can't be extracted).
       Unifying a meta with Tdummy would not resolve it usefully. *)
    let non_dummy_bind_tys = filter_value_types bind_tys in
    let () =
      match non_dummy_bind_tys with
      | elem_ty :: _ -> List.iter (fun (_, ty) -> try_mgu ty elem_ty) ids'
      | [] -> ()
    in
    let ids, env =
      push_vars'
        (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids')
        env
    in
    push_env_types ids;
    (* The continuation's lambda parameter adds one de Bruijn level.
       Shift move tracking sets so that parent-scope owned-variable indices
       stay in sync with the body's coordinate system.  Without this shift,
       after N bind continuations the indices drift by N, causing spurious
       collisions that produce incorrect std::move (use-after-move). *)
    let add_owned =
      match ids with
      | (_, ty) :: _ when Escape.is_shared_ptr_type ty -> Some 1
      | _ -> None
    in
    with_shifted_move_tracking 1 ?add_owned (fun () ->
    match ids with
    | (x, ml_ty) :: _ ->
      let tvars = get_current_type_vars () in
      let ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ml_ty in
      if ty == Tvoid || ty == Tunknown || ml_type_is_unit ml_ty then
        (* Unit/void bind result: execute the action for side effects,
           then declare the variable as Unit::e_TT so the continuation
           can reference it if needed. *)
        let action_is_pure_ret =
          match a_ml with
          | MLapp (MLglob (r, _), _) when is_ret r -> true
          | _ -> false
        in
        let side_effect =
          match a with
          | CPPenum_val _ -> []
          | _ when action_is_pure_ret -> []
          | _ -> [Sexpr a]
        in
        (* Generate the continuation first, then check if the variable is
           actually referenced in the generated C++ (unit-match elimination
           and Ret-in-void optimization may drop ML-level references). *)
        let body = gen_stmts env k f in
        let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty tvars ml_ty in
        let decl =
          if not (stmts_reference_var x body) then []
          else if ml_type_is_unit ml_ty && not (is_cpp_unit_type cpp_ty) then
            []
          else if ml_type_is_unit ml_ty then
            [Sasgn (x, Some cpp_ty, mk_tt_expr ())]
          else
            []
        in
        side_effect @ decl @ body
      else begin
        match extract_block_template a with
        | Some (ref, tmpl, args, tys) ->
          Sblock_custom (ref, tmpl, x, ty, args, tys)
          :: gen_stmts env k f
        | None ->
          Sasgn (x, Some ty, a) :: gen_stmts env k f
      end
    | _ ->
      (* No lambda parameters (eta-reduced continuation like bare Ret).
         Execute the action for side effects, then run the continuation. *)
      let side_effect =
        match a with CPPenum_val _ -> [] | _ -> [Sexpr a]
      in
      ( match f with
      | MLglob (r, _) when is_ret r ->
        (* Eta-reduced Ret: bind action Ret = action (monad right identity).
           In sequential mode, just execute the action and return. *)
        if tctx.current_cpp_return_type = Some Tvoid then
          side_effect @ [Sreturn None]
        else
          [k a]
      | _ ->
        (* Eta-reduced non-Ret continuation: f is a bare function reference.
           Bind action result to a temp var and apply f to it, instead of
           discarding the result and returning f unapplied. *)
        let tvars = get_current_type_vars () in
        let non_void_ty =
          match non_dummy_bind_tys with
          | ty :: _ ->
            let cpp_ty =
              convert_ml_type_to_cpp_type env Refset'.empty tvars ty
            in
            if cpp_ty = Tvoid || cpp_ty = Tunknown || ml_type_is_unit ty then
              None
            else
              Some cpp_ty
          | [] -> None
        in
        ( match non_void_ty with
        | Some cpp_ty ->
          let temp_id = Id.of_string "_bind_result" in
          let f_expr = gen_expr env f in
          let app = CPPfun_call (f_expr, [CPPvar temp_id]) in
          [Sasgn (temp_id, Some cpp_ty, a); k app]
        | None ->
          side_effect @ gen_stmts env k f ) ) )
    end
  | MLapp (MLglob (r, _), a1 :: l) when is_ret r ->
    if tctx.itree_mode = Reified then begin
      (* Reified mode: Ret is a constructor call, not desugared. *)
      let saved_dead = tctx.move_dead_after in
      let e = gen_tail_expr env ast in
      let result = inline_iife k e in
      tctx.move_dead_after <- saved_dead;
      result
    end
    else begin
      (* Sequential mode: eliminate Ret, just use the value. *)
      let t = Common.last (a1 :: l) in
      if tctx.current_cpp_return_type = Some Tvoid then
        (* Void-returning function: discard the value and return. *)
        [Sreturn None]
      else
        [k (gen_expr env t)]
    end
  | MLcase (typ, t, pv) when is_custom_match pv ->
    (* Set up dead-after for owned variables at their last use, same as the
       default tail-position case below. Without this, unique_ptr variables
       passed as function arguments in the scrutinee would not get std::move.
       Suppress when processing a let-binding RHS to avoid use-after-move. *)
    let saved_dead = tctx.move_dead_after in
    ( if not tctx.move_suppress_tail then
        let tail_dead =
          Escape.IntSet.filter
            (fun i -> Escape.nb_occur_match i ast = 1)
            tctx.move_owned_vars
        in
        tctx.move_dead_after <-
          Escape.IntSet.union tctx.move_dead_after tail_dead );
    let result = gen_custom_cpp_case env k typ t pv in
    tctx.move_dead_after <- saved_dead;
    result
  | MLcons (_, r, []) when Table.is_tt_constructor r
      && tctx.current_cpp_return_type = Some Tvoid ->
    (* tt (unit constructor) in tail position of a void-returning function *)
    if tctx.itree_mode = Reified then begin
      Table.require_itree_header ();
      [k (mk_itree_ret Tvoid [])]
    end
    else
      [Sreturn None]
  | MLglob (r, _) when is_ghost r ->
    if tctx.itree_mode = Reified then begin
      (* Reified mode: ghost (void value) at tail position must produce
         ITree<void>::ret() rather than bare return, since the function
         returns shared_ptr<ITree<void>>. *)
      Table.require_itree_header ();
      [k (mk_itree_ret Tvoid [])]
    end
    else
      [Sreturn None]
  | MLexn msg ->
    (* Generate throw statement for unreachable/absurd cases (e.g., empty
       match) *)
    [Sthrow msg]
  | MLmagic (MLexn msg) ->
    (* Handle MLexn wrapped in MLmagic *)
    [Sthrow msg]
  | MLcase (typ, t, pv)
    when (not (record_fields_of_type typ == [])) && Array.length pv == 1 ->
    let ids, _r, _pat, body = pv.(0) in
    let n = List.length ids in
    let body' = match body with MLmagic b -> b | b -> b in
    let is_simple =
      match body' with
      | MLrel i when i <= n -> true
      | MLapp (MLrel i, _) when i <= n -> true
      | MLapp (MLmagic (MLrel i), _) when i <= n -> true
      | _ -> false
    in
    if is_simple then
      (* Simple body: gen_expr handles these as direct field access (no IIFE),
         so delegate to the default path. *)
      let saved_dead = tctx.move_dead_after in
      ( if not tctx.move_suppress_tail then
          let tail_dead =
            Escape.IntSet.filter
              (fun i -> Escape.nb_occur_match i ast = 1)
              tctx.move_owned_vars
          in
          tctx.move_dead_after <-
            Escape.IntSet.union tctx.move_dead_after tail_dead );
      let result = inline_iife k (gen_expr env ast) in
      tctx.move_dead_after <- saved_dead;
      result
    else
      (* Complex body: emit field extraction assignments as flat statements
         instead of wrapping in an IIFE. This produces clean code for all
         continuations (return, assignment, etc.). *)
      let is_typeclass = Table.is_typeclass_type typ in
      let all_fields = record_fields_of_type typ in
      let non_erased_fields = List.filter_map Fun.id all_fields in
      let make_field_access base_expr fld =
        if is_typeclass then
          let fld_name = Id.of_string (Common.pp_global_name Term fld) in
          CPPqualified (base_expr, fld_name)
        else
          CPPget' (base_expr, fld)
      in
      let renamed_ids, env' =
        push_vars'
          (List.rev_map
             (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
             ids )
          env
      in
      let renamed_ids_fwd = List.rev renamed_ids in
      let tvars = get_current_type_vars () in
      let asgns =
        List.mapi
          (fun i ((renamed_name, _), (_, ty)) ->
            let fld =
              try Some (List.nth non_erased_fields i) with _ -> None
            in
            let e =
              match fld with
              | Some fld -> make_field_access (gen_expr env t) fld
              | _ ->
                CErrors.anomaly (Pp.str "record field index out of bounds")
            in
            let e =
              match typ with
              | Tglob (record_ref, _, _) ->
                let storage_ty =
                  convert_ml_type_to_cpp_type
                    env
                    (Refset'.add record_ref Refset'.empty)
                    tvars
                    ty
                in
                let api_ty =
                  convert_ml_type_to_cpp_type env Refset'.empty tvars ty
                in
                wrap_api_expr ~storage_ty ~api_ty e
              | _ -> e
            in
            Sasgn
              ( renamed_name,
                Some (convert_ml_type_to_cpp_type env Refset'.empty tvars ty),
                e ) )
          (List.combine renamed_ids_fwd ids)
      in
      push_env_types
        (List.map
           (fun ((n, _), (_, ty)) -> (n, ty))
           (List.combine renamed_ids_fwd ids) );
      asgns @ gen_stmts env' k body
  | t ->
    (* Tail position: generate expression with dead-after tracking.
       No deref_reified needed: in sequential mode, monadic variables are
       direct values (bind desugars to let-binding); in reified mode,
       they are trees returned as-is. *)
    let saved_dead = tctx.move_dead_after in
    let is_void_tail = match t with
      | MLapp (f, args) | MLmagic (MLapp (f, args)) ->
        ml_callee_is_void f
        (* Only treat as void if fully applied — partial applications
           return a function value, not void. *)
        && ( match f with
           | MLglob (r, _) ->
             ( match find_type_opt r with
             | Some ty ->
               let rec count_arrows = function
                 | Miniml.Tarr (t1, rest) ->
                   if isTdummy t1 then count_arrows rest
                   else 1 + count_arrows rest
                 | _ -> 0
               in
               let n_non_dummy_args =
                 List.length (List.filter (fun a ->
                   match a with MLdummy _ -> false | _ -> true) args)
               in
               n_non_dummy_args >= count_arrows ty
             | None -> true )
           | _ -> true )
      | _ -> false
    in
    if is_void_tail then begin
      let e = gen_tail_expr env t in
      tctx.move_dead_after <- saved_dead;
      if tctx.current_cpp_return_type = Some Tvoid then
        [Sexpr e; Sreturn None]
      else
        match k (CPPint 0) with
        | Sexpr _ ->
          (* Side-effect-only continuation (e.g. from unit let handler).
             The void call provides the side effect; the caller handles
             the variable declaration separately.  No value needed. *)
          [Sexpr e]
        | _ ->
          [Sexpr e] @ inline_iife k (mk_tt_expr ())
    end
    else begin
      let e = gen_tail_expr env t in
      let result = inline_iife k e in
      tctx.move_dead_after <- saved_dead;
      result
    end

(** Generate a C++ expression for [t] in tail position.
    Marks owned variables that occur exactly once as dead-after (for
    last-use move semantics).  Callers are responsible for saving and
    restoring [move_dead_after].

    Used by the default tail case and by reified-mode bind/ret handlers
    (which bypass monadic desugaring and treat bind/Ret as plain calls). *)
and gen_tail_expr env t =
  ( if not tctx.move_suppress_tail then
      let tail_dead =
        Escape.IntSet.filter
          (fun i -> Escape.nb_occur_match i t = 1)
          tctx.move_owned_vars
      in
      tctx.move_dead_after <-
        Escape.IntSet.union tctx.move_dead_after tail_dead );
  gen_expr env t

(** Generate a fixpoint (recursive function) definition. Handles both single and
    mutually recursive functions. [all_fix_ids] contains names of all mutual
    fixpoints; [fix_idx] is the index of this fixpoint in the mutual group. *)
and gen_fix env ?(all_fix_ids = []) ~fix_idx (n, ty) f =
  let ids, f = collect_lams f in
  let ids, _ =
    push_vars'
      (List.map (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty)) ids)
      env
  in
  (* Push all mutual fixpoint names (or just (n,ty) for single fixpoints). For
     mutual fixpoints, all_fix_ids contains all fixpoint names in array order.
     For single fixpoints, all_fix_ids is empty and we use [(n,ty)].

     IMPORTANT: Rocq's extraction pushes fix bindings so that the LAST function
     is at db 1 and the FIRST is at db n (standard de Bruijn convention with
     fold_left over the array). We must reverse fix_names to match. *)
  let fix_names = if all_fix_ids = [] then [(n, ty)] else all_fix_ids in
  let n_fix_funs = List.length fix_names in
  let fix_names_db_order = List.rev fix_names in
  let renamed_fix_ids, env = push_vars' (ids @ fix_names_db_order) env in
  let saved_env_types = tctx.env_types in
  push_env_types (ids @ fix_names_db_order);
  (* Extract the renamed name for THIS fixpoint function. fix_names_db_order
     is reversed from the array order, so fix array index i corresponds to
     position (n_fix_funs - 1 - i) in the reversed list. *)
  let n_lam_params = List.length ids in
  let renamed_n =
    fst (List.nth renamed_fix_ids
           (n_lam_params + (n_fix_funs - 1 - fix_idx))) in
  let ids = List.filter (fun (_, ty) -> not (ml_type_is_void ty)) ids in
  (* Phase 2: set up move state for fixpoint body. Fix params are owned (passed
     by value in the generated std::function lambda). After push_vars'(ids @
     fix_names), de Bruijn indices in f are: ids[0] → db 1, ..., ids[k-1] → db
     k, fix_names[0] → db k+1, ..., fix_names[m-1] → db k+m. We only mark lambda
     params as owned (not the fix self-references). *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let n_fix_params = List.length ids in
  let fix_owned = Escape.infer_owned_params (n_fix_params + n_fix_funs) f in
  tctx.move_owned_vars <-
    List.fold_left
      (fun acc i ->
        let db = i + 1 in
        (* ids[i] has db index i+1 *)
        let owned =
          match List.nth_opt fix_owned i with
          | Some b -> b
          | None -> false
        in
        let ml_ty = snd (List.nth ids i) in
        if owned && Escape.is_shared_ptr_type ml_ty then
          Escape.IntSet.add db acc
        else
          acc )
      Escape.IntSet.empty
      (List.init n_fix_params (fun i -> i));
  tctx.move_dead_after <- Escape.IntSet.empty;
  tctx.move_n_params <- n_fix_params + n_fix_funs;
  let result =
    ((renamed_n, ty), ids, gen_stmts env (fun x -> Sreturn (Some x)) f)
  in
  tctx.env_types <- saved_env_types;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  result

(** Generate C++ namespace with constructor factory functions for an inductive
    type.
    @param consarg_names  binder names from {!Miniml.ml_ind_packet.ip_consarg_names};
      when provided, struct fields use descriptive names instead of [d_aJ]. *)
let gen_ind_cpp ?(consarg_names = [||]) vars name cnames tys =
  let constrdecl =
    Array.to_list
      (Array.mapi
         (fun i tys ->
           let c = cnames.(i) in
           let ctor_struct_name = ctor_struct_name_of_ref ~fallback_idx:i c in
           let ctor_consarg_names =
             if i < Array.length consarg_names then consarg_names.(i)
             else []
           in
           let n_fields = List.length tys in
           let field_ids =
             compute_and_register_field_names
               ctor_struct_name ctor_consarg_names n_fields
           in
           let constr =
             List.mapi
               (fun i x ->
                 ( List.nth field_ids i,
                   convert_ml_type_to_cpp_type
                     (empty_env ())
                     (Refset'.add name Refset'.empty)
                     vars
                     x ) )
               tys
           in
           let make_args =
             List.map
               (fun (x, _) -> mk_cppglob_local (GlobRef.VarRef x) [])
               constr
           in
           let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
           let make =
             Dfundef
               ( [(c, []); (GlobRef.VarRef (Id.of_string "make"), [])],
                 Tshared_ptr (Tglob (name, ty_vars, [])),
                 List.rev constr,
                 [
                   Sreturn
                     (Some
                        (CPPfun_call
                           ( CPPmk_shared (Tglob (name, ty_vars, [])),
                             [CPPstruct (c, ty_vars, make_args)] ) ) );
                 ],
                 false )
           in
           (ty_vars == [], make) )
         tys )
    |> List.filter_map (fun (keep, make) -> if keep then Some make else None)
  in
  Dnspace (Some name, constrdecl)

(* =========================================================================
   Shared helpers for record and typeclass generation
   ========================================================================= *)

(** Count the actual (non-promoted) type parameters in [ip_sign].  Entries
    marked [Keep] correspond to real template parameters; the remaining
    entries are promoted Type-valued fields. *)
let count_keep_params sign =
  List.length (List.filter (fun x -> x == Keep) sign)

(** Filter [Tdummy] entries from the first constructor's type list.  Both
    [gen_record_cpp] and [gen_typeclass_cpp] need the non-erased types only,
    because [select_fields] already drops the corresponding field names. *)
let non_dummy_constructor_types ind =
  filter_value_types ind.ip_types.(0)

(** Generate C++ struct for a record type.

    Only actual type parameters ([Keep] in [ip_sign]) become C++ template
    parameters.  Promoted Type-valued fields (present in [ip_vars] but past
    the [Keep] entries) are erased to [std::any] — they have no C++ template
    counterpart in a plain struct (unlike typeclasses, which turn them into
    [typename I::field] requirements). *)
let gen_record_cpp name fields ind =
  let nb_keep = count_keep_params ind.ip_sign in
  let param_ip_vars = List.filteri (fun i _ -> i < nb_keep) ind.ip_vars in
  let vars = List.map Common.tparam_name param_ip_vars in
  (* Use full ip_vars for type name resolution so Tvars resolve to names,
     then replace promoted Tvars (not in template params) with std::any. *)
  let all_vars = List.map Common.tparam_name ind.ip_vars in
  let promoted_var_names =
    List.filteri (fun i _ -> i >= nb_keep) ind.ip_vars
    |> List.map (fun id -> Id.to_string (Common.tparam_name id))
  in
  let replace_promoted = function
    | Tvar (_, Some id) when List.mem (Id.to_string id) promoted_var_names ->
      Tany
    | Tglob (g, _, _) when Table.is_promoted_type_var g ->
      ( match Table.promoted_type_var_name g with
      | Some var_id when List.mem (Id.to_string var_id) promoted_var_names ->
        Tany
      | _ -> Tany )
    | ty -> ty
  in
  let l = List.combine fields (non_dummy_constructor_types ind) in
  let l =
    List.mapi
      (fun i (x, t) ->
        let n =
          match x with
          | Some n -> n
          | None -> GlobRef.VarRef (Id.of_string ("_field" ^ string_of_int i))
        in
        let ct =
          convert_ml_type_to_cpp_type
            (empty_env ())
            (Refset'.add name Refset'.empty)
            all_vars
            t
        in
        let ct = Minicpp.map_cpp_type replace_promoted ct in
        ( Fvar' (n, ct), VPublic, SNoTag ) )
      l
  in
  let self_ty =
    Tglob (name, List.mapi (fun i x -> Tvar (i, Some x)) vars, [])
  in
  let record_value_compat_methods =
    let clone_method =
      let clone_args =
        List.filter_map
          (function
            | Fvar' (field_ref, field_ty), _, _ ->
              Some
                (gen_clone_field_expr ~src_ty:field_ty ~dst_ty:field_ty
                   (CPPget' (CPPderef CPPthis, field_ref)))
            | _ -> None)
          l
      in
      ( Fmethod
          {
            mf_name = Id.of_string "clone";
            mf_tparams = [];
            mf_ret_type = self_ty;
            mf_params = [];
            mf_body = [Sreturn (Some (CPPstruct (name, List.mapi (fun i x -> Tvar (i, Some x)) vars, clone_args)))];
            mf_is_const = true;
            mf_is_static = false;
            mf_is_inline = false;
            mf_this_pos = 0;
            mf_no_pure = false;
          },
        VPublic,
        SAccessors )
    in
    [clone_method]
  in
  let ty_vars = List.map (fun x -> (TTtypename, x)) vars in
  Dstruct
    {
      ds_ref = name;
      ds_fields = l @ record_value_compat_methods;
      ds_tparams = ty_vars;
      ds_constraint = None;
      ds_needs_shared_from_this = false;
    }

(** Generate a C++ concept from a type class.
   Type class Eq(A) with method eqb : A -> A -> bool becomes:
   template<typename I, typename A>
   concept Eq = requires(A a0, A a1) {
     { I::eqb(a0, a1) } -> std::convertible_to<bool>;
   };

   Uses CPPconvertible_to with the actual cpp_type for the constraint,
   which will be pretty-printed in cpp.ml.
*)
let gen_typeclass_cpp name fields ind =
  let inst_id = Id.of_string "I" in
  let nb_keep = count_keep_params ind.ip_sign in
  (* Split ip_vars into param vars (real type params) and promoted vars
     (associated types). Prefix param vars with t_ for BDE convention. *)
  let prefixed_ip_vars =
    List.mapi
      (fun i x -> if i < nb_keep then Common.tparam_name x else x)
      ind.ip_vars
  in
  let param_vars = List.filteri (fun i _ -> i < nb_keep) prefixed_ip_vars in
  let promoted_vars =
    List.filteri (fun i _ -> i >= nb_keep) prefixed_ip_vars
  in
  (* Only param vars become concept template parameters; promoted vars become
     typename requirements inside the requires block *)
  let ty_vars = List.map (fun x -> (TTtypename, x)) param_vars in
  let all_params = (TTtypename, inst_id) :: ty_vars in
  (* Build typename requirements for promoted vars: typename I::field; *)
  let type_reqs =
    List.map
      (fun var_id -> Tqualified (Tvar (0, Some inst_id), var_id))
      promoted_vars
  in
  let non_dummy_types = non_dummy_constructor_types ind in
  let method_list =
    ( try List.combine fields non_dummy_types
      with _ ->
        List.map (fun f -> (f, Miniml.Tunknown)) fields )
  in
  (* Build a mapping for promoted vars from nested typeclasses.

     When a promoted field has typeclass type (e.g., [base_category :
     PreCategory]), the nested typeclass's own promoted vars (e.g., [Obj])
     may appear in other fields' types (e.g., [zero_object : Obj
     base_category]).  During extraction, these become [Tvar(1000, Some
     "Obj")] — indistinguishable from a direct promoted var of the current
     typeclass.

     We build a mapping [Obj → typename I::base_category::Obj] so that
     [subst_promoted_in_cpp_type] can resolve them correctly through the
     promoted field rather than leaving a dangling bare [Obj]. *)
  let nested_promoted_map =
    List.concat_map
      (fun (field_opt, field_ty) ->
        match (field_opt, field_ty) with
        | Some _field_ref, Miniml.Tglob (r, _, _) when Table.is_typeclass r ->
          let field_name_str = Common.pp_global_name Term _field_ref in
          let field_id = Id.of_string field_name_str in
          if List.exists (Id.equal field_id) promoted_vars then
            let nested_ip_vars = Table.get_ind_ip_vars r in
            let nested_nb_keeps = Table.get_ind_nb_sign_keeps r in
            let nested_promoted =
              List.filteri (fun i _ -> i >= nested_nb_keeps) nested_ip_vars
            in
            List.map
              (fun nested_var ->
                ( nested_var,
                  Tqualified
                    (Tqualified (Tvar (0, Some inst_id), field_id), nested_var)
                ) )
              nested_promoted
          else
            []
        | _ -> [] )
      method_list
  in
  (* Substitute promoted Tvars with [Tqualified(I, name)] in cpp_type trees.
     After conversion, promoted vars appear as [Tvar(_, Some name)] where
     name is in [promoted_vars].  Replace with [typename I::name].
     Also handles nested promoted vars from typeclass-typed promoted fields
     via [nested_promoted_map] — e.g., [Obj] from [PreCategory] becomes
     [typename I::base_category::Obj] when [base_category] is a promoted
     [PreCategory]-typed field. *)
  let rec subst_promoted_in_cpp_type = function
    | Tvar (_, Some vname) when List.exists (Id.equal vname) promoted_vars ->
      Tqualified (Tvar (0, Some inst_id), vname)
    | Tvar (_, Some vname) -> (
      match
        List.find_opt (fun (n, _) -> Id.equal n vname) nested_promoted_map
      with
      | Some (_, replacement) -> replacement
      | None -> Tvar (0, Some vname) )
    | Tfun (args, ret) ->
      Tfun
        ( List.map subst_promoted_in_cpp_type args,
          subst_promoted_in_cpp_type ret )
    | Tglob (r, ts, es) -> Tglob (r, List.map subst_promoted_in_cpp_type ts, es)
    | Tshared_ptr t -> Tshared_ptr (subst_promoted_in_cpp_type t)
    | Tunique_ptr t -> Tunique_ptr (subst_promoted_in_cpp_type t)
    | Tnamespace (r, t) -> Tnamespace (r, subst_promoted_in_cpp_type t)
    | Tqualified (b, id) -> Tqualified (subst_promoted_in_cpp_type b, id)
    | Tref t -> Tref (subst_promoted_in_cpp_type t)
    | Tvariant ts -> Tvariant (List.map subst_promoted_in_cpp_type ts)
    | Tid (id, ts) -> Tid (id, List.map subst_promoted_in_cpp_type ts)
    | Tid_external (id, ts) -> Tid_external (id, List.map subst_promoted_in_cpp_type ts)
    | Tmod (m, t) -> Tmod (m, subst_promoted_in_cpp_type t)
    | t -> t
  in
  (* Check if a type is a bare promoted Tvar — a Tvar whose index is beyond the
     real type parameters. This indicates the field's type is entirely
     determined by a promoted associated type, so we can't decompose it into
     args and return type at concept time (the concrete type might be a
     function). *)
  let is_bare_promoted_tvar ty =
    match ty with
    | Miniml.Tvar n -> n > nb_keep
    | _ -> false
  in
  (* Check if a field type is a typeclass-typed promoted field.  Such
     fields become [typename I::field] requirements (already in type_reqs)
     and should NOT generate method requirements in the concept body. *)
  let is_typeclass_field_type ty =
    match ty with
    | Miniml.Tglob (r, _, _) -> Table.is_typeclass r
    | _ -> false
  in
  (* Generate a single method requirement. Returns either: - `Normal (params,
     (call, constraint))` for regular methods - `Disjunctive expr` for fields
     whose type is a bare promoted Tvar *)
  let gen_method_req (field_opt, field_ty) =
    match field_opt with
    | None -> None (* Anonymous field, skip *)
    | Some field_ref ->
      let method_name = Common.pp_global_name Term field_ref in
      if is_typeclass_field_type field_ty then
        (* TypeClass-typed field — skip method requirement.  The field
           is promoted and already has a [typename I::field;] type
           requirement in [type_reqs].  Adding a method requirement
           would try to use the concept name as a concrete type
           (e.g., [std::shared_ptr<PreCategory>]) which is invalid. *)
        None
      else if is_bare_promoted_tvar field_ty then
        (* Field type is a bare promoted Tvar (e.g., fun_ind_prf :
           fun_ind_prf_ty). The concrete type could be a plain value or a
           function with any arity. Generate a disjunctive concept requirement:
           requires { { I::method() } -> std::convertible_to<T>; } || requires {
           { I::method } -> std::convertible_to<T>; } The first clause handles
           nullary accessors (Meyers singleton pattern). The second handles
           functions (pointer converts to std::function) and static data members
           (direct value). *)
        let ret_cpp =
          convert_ml_type_to_cpp_type
            (empty_env ())
            Refset'.empty
            prefixed_ip_vars
            field_ty
        in
        let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
        let constraint_expr = CPPconvertible_to ret_cpp in
        let qualified =
          CPPqualified (CPPvar inst_id, Id.of_string method_name)
        in
        let call_form =
          CPPrequires ([], [(CPPfun_call (qualified, []), constraint_expr)], [])
        in
        let value_form = CPPrequires ([], [(qualified, constraint_expr)], []) in
        Some (`Disjunctive (CPPbinop ("||", call_form, value_form)))
      else
        let args, ret = get_args_and_ret [] field_ty in
        (* Filter out type class instance arguments (they're passed via
           template) *)
        let args =
          List.filter (fun t -> not (Table.is_typeclass_type t)) args
        in
        let ret_cpp =
          convert_ml_type_to_cpp_type
            (empty_env ())
            Refset'.empty
            prefixed_ip_vars
            ret
        in
        let ret_cpp = subst_promoted_in_cpp_type ret_cpp in
        (* Create parameter names: a0, a1, a2, ... *)
        let params =
          List.mapi
            (fun j arg_ty ->
              let arg_cpp =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  Refset'.empty
                  prefixed_ip_vars
                  arg_ty
              in
              let arg_cpp = subst_promoted_in_cpp_type arg_cpp in
              (arg_cpp, Id.of_string ("a" ^ string_of_int j)) )
            args
        in
        (* Method call: I::method_name(a0, a1, ...).  CPPfun_call stores
           args reversed (the printer applies List.rev when rendering),
           so we pre-reverse to get the correct printed order. *)
        let call_args = List.rev_map (fun (_, id) -> CPPvar id) params in
        let call =
          CPPfun_call
            (CPPqualified (CPPvar inst_id, Id.of_string method_name), call_args)
        in
        (* Constraint: use the cpp_type directly - cpp.ml will render it *)
        let constraint_expr = CPPconvertible_to ret_cpp in
        Some (`Normal (params, (call, constraint_expr)))
  in
  let all_reqs =
    List.filter_map (fun pair -> gen_method_req pair) method_list
  in
  (* Separate normal requirements from disjunctive ones *)
  let normal_reqs =
    List.filter_map
      (function
        | `Normal r -> Some r
        | _ -> None )
      all_reqs
  in
  let disjunctive_exprs =
    List.filter_map
      (function
        | `Disjunctive e -> Some e
        | _ -> None )
      all_reqs
  in
  (* Build the concept body. Normal requirements go in a single requires{}
     block. Disjunctive requirements (for bare-Tvar fields) are &&-ed
     separately, each wrapped in parentheses via the || rendering. *)
  let concept_body =
    let normal_part =
      if normal_reqs = [] then
        None
      else
        let all_params_flat = List.concat_map fst normal_reqs in
        let seen = ref [] in
        let dedup_params =
          List.filter
            (fun (_ty, id) ->
              let key = Id.to_string id in
              if List.mem key !seen then
                false
              else (
                seen := key :: !seen;
                true ) )
            all_params_flat
        in
        let constraints = List.map snd normal_reqs in
        Some (CPPrequires (dedup_params, constraints, type_reqs))
    in
    match (normal_part, disjunctive_exprs) with
    | Some np, [] -> np
    | None, [d] ->
      if type_reqs <> [] then
        CPPbinop ("&&", CPPrequires ([], [], type_reqs), d)
      else
        d
    | None, d :: rest ->
      let base =
        if type_reqs <> [] then
          CPPbinop ("&&", CPPrequires ([], [], type_reqs), d)
        else
          d
      in
      List.fold_left (fun acc e -> CPPbinop ("&&", acc, e)) base rest
    | Some np, ds -> List.fold_left (fun acc e -> CPPbinop ("&&", acc, e)) np ds
    | None, [] ->
      if type_reqs <> [] then
        CPPrequires ([], [], type_reqs)
      else
        CPPrequires ([], [], [])
    (* degenerate: no requirements *)
  in
  Dtemplate (all_params, None, Dconcept (name, concept_body))

(** Generate a C++ struct for a type class instance.
   Type class instances become structs with static methods.
   Example: Instance IntEq : Eq int := { eqb := Int.eqb }.
   becomes: struct IntEq { static bool eqb(int a, int b) { ... } };

   Returns: (struct_decl option, class_ref option, type_args)
   The class_ref and type_args are used to generate static_assert in cpp.ml *)
let gen_instance_struct (name : GlobRef.t) (body : ml_ast) (ty : ml_type) :
    cpp_decl option * GlobRef.t option * ml_type list =
  (* For parameterized instances, strip Tarr/MLlam layers to get to the inner
     typeclass type and constructor body. Collect template parameters along the
     way. Example: numOption has type Tarr(Tdummy, Tarr(Tglob(Numeric,[A],[]),
     Tglob(Numeric,[option A],[]))) and body MLlam(_, Tdummy, MLlam(_,
     Tglob(Numeric,...), MLcons(...))) *)
  let rec strip_outer_layers ty body tc_idx tc_acc lam_acc =
    match (ty, body) with
    | Tarr (arg_ty, rest_ty), MLlam (ml_id, lam_ty, rest_body) ->
      if Mlutil.isTdummy arg_ty then
        (* Erased type parameter — skip (template params are inferred from type
           variables in the return type via collect_ml_tvars below) *)
        strip_outer_layers
          rest_ty
          rest_body
          tc_idx
          tc_acc
          ((id_of_mlid ml_id, lam_ty) :: lam_acc)
      else if Table.is_typeclass_type arg_ty then
        (* Typeclass constraint — becomes a concept-constrained template
           parameter.  E.g., [PreCategory _tcI0] instead of [typename
           _tcI0], so the compiler enforces concept satisfaction. *)
        let instance_name = tc_instance_id tc_idx in
        let tt =
          match arg_ty with
          | Tglob (r, _, _) ->
            (* Only use inline concept constraint for unary concepts.
               A concept is unary iff it has no kept type variables
               (nb_sign_keeps = 0), so its only template param is I.
               Multi-parameter concepts like [Numeric<I, t_A>] cannot
               use inline syntax because the remaining type args aren't
               available at the template-param declaration site. *)
            let nb_keeps = Table.get_ind_nb_sign_keeps r in
            if nb_keeps = 0 then TTconcept r else TTtypename
          | _ -> TTtypename
        in
        strip_outer_layers
          rest_ty
          rest_body
          (tc_idx + 1)
          ((tt, instance_name) :: tc_acc)
          ((instance_name, lam_ty) :: lam_acc)
      else (* Not a type param or typeclass — stop stripping *)
        (ty, body, List.rev tc_acc, List.rev lam_acc)
    | _ -> (ty, body, List.rev tc_acc, List.rev lam_acc)
  in
  let inner_ty, inner_body, tc_temps, lam_params =
    strip_outer_layers ty body 0 [] []
  in
  (* Collect type variables from the inner return type's type args. For
     parameterized instances like numOption : Numeric (option A), the return
     type is Tglob(Numeric, [option A], []) which contains Tvar for A. These
     need to become template typename parameters (T1, T2, etc.). *)
  let rec collect_ml_tvars acc = function
    | Miniml.Tvar i ->
      if List.mem i acc then
        acc
      else
        i :: acc
    | Miniml.Tarr (t1, t2) -> collect_ml_tvars (collect_ml_tvars acc t1) t2
    | Miniml.Tglob (_, tys, _) -> List.fold_left collect_ml_tvars acc tys
    | _ -> acc
  in
  let tv_temps =
    match inner_ty with
    | Tglob (_, type_args, _) ->
      let raw = List.fold_left collect_ml_tvars [] type_args in
      List.sort compare raw
      |> List.mapi (fun i _ -> (TTtypename, tvar_id (i + 1)))
    | _ -> []
  in
  (* Template params: typeclass params first, then type vars (matches gen_dfun
     convention) *)
  let template_params = tc_temps @ tv_temps in
  (* Now inner_ty should be Tglob(class_ref, type_args, _) and inner_body should
     be MLcons(...) *)
  match inner_ty with
  | Tglob (class_ref, type_args, _) when Table.is_typeclass class_ref ->
    (* Get the type class fields (method names) and field types (from
       ind_packet) *)
    let fields = Table.record_fields_of_type inner_ty in
    let field_types =
      List.filter
        (fun t -> not (Mlutil.isTdummy t))
        (Table.record_field_types class_ref)
    in
    (* Strip MLmagic wrapper if present — promoted dependent records may have
       their constructor wrapped in MLmagic due to Tvar/Tglob mismatches during
       extraction unification. *)
    let inner_body =
      match inner_body with
      | MLmagic b -> b
      | b -> b
    in
    ( match inner_body with
    | MLcons (cons_ty, _ctor_ref, method_bodies) ->
      (* For promoted dependent records, the definition type Tglob(Magma,[],[])
         has no type_args, but the MLcons type Tglob(Magma,[nat],[]) carries the
         concrete types extracted from the erased constructor args. *)
      let type_args =
        match cons_ty with
        | Tglob (_, ta, _) when ta <> [] -> ta
        | _ -> type_args
      in
      (* Register promoted type bindings for this instance so that call sites
         (eta_fun) can substitute promoted Tvars with concrete types. E.g., for
         nat_magma : Magma, register [(carrier, nat)] so pick_op<nat_magma>
         eta-expansion uses unsigned int instead of std::any. *)
      let ip_vars = Table.get_ind_ip_vars class_ref in
      let nb_sign_keeps_inst = Table.get_ind_nb_sign_keeps class_ref in
      let promoted_vars =
        List.filteri (fun i _ -> i >= nb_sign_keeps_inst) ip_vars
      in
      let promoted_concrete =
        if List.length type_args > nb_sign_keeps_inst then
          List.filteri (fun i _ -> i >= nb_sign_keeps_inst) type_args
        else
          []
      in
      if
        List.length promoted_vars = List.length promoted_concrete
        && promoted_vars <> []
      then
        Table.add_instance_promoted_types
          name
          (List.map2
             (fun var_name ml_ty -> (var_name, ml_ty))
             promoted_vars
             promoted_concrete );
      (* Build the environment with lambda parameters for de Bruijn resolution.
         For parameterized instances, method bodies reference the outer lambda
         parameters (e.g., the typeclass dictionary) via MLrel indices. We push
         lam_params into the env so these references resolve correctly. *)
      let base_env = snd (push_vars' (List.rev lam_params) (empty_env ())) in
      (* Collect type var names for convert_ml_type_to_cpp_type *)
      let type_var_names = List.map snd tv_temps in
      (* Set up type variable context for fixpoint lifting. Without this,
         fixpoints inside methods get lifted with wrong names and missing
         template parameters. *)
      let saved_outer_name = tctx.current_outer_function_name in
      tctx.current_outer_function_name <- Some (Common.pp_global_name Term name);
      set_current_type_vars type_var_names;
      (* Generate static methods for each field *)
      let gen_method (field_ref, field_ml_ty) field_body =
        match field_ref with
        | None -> None (* Anonymous field, skip *)
        | Some method_ref ->
          (* Skip typeclass-typed fields — they are promoted and handled
             by [using] declarations, not methods.  E.g., [base_category :
             PreCategory] becomes [using base_category = ...;], not a
             static method returning the typeclass. *)
          let is_tc_field =
            match field_ml_ty with
            | Miniml.Tglob (r, _, _) -> Table.is_typeclass r
            | _ -> false
          in
          if is_tc_field then
            None
          else
          let method_name =
            Id.of_string (Common.pp_global_name Term method_ref)
          in
          (* Strip MLmagic wrappers from the field body — promoted dependent
             records produce MLmagic due to Tvar/Tglob mismatches. *)
          let rec strip_magic = function
            | MLmagic b -> strip_magic b
            | b -> b
          in
          let field_body = strip_magic field_body in
          (* Substitute type class parameter with instance's type arg in the
             field type. This gives us the concrete return type (e.g., bool for
             eqb: A -> A -> bool). For promoted dependent records, type_args may
             be empty, leaving Tvars unsubstituted — we handle that below by
             using lambda binder types. *)
          let subst_ty = Mlutil.type_subst_list type_args field_ml_ty in
          (* Extract parameter names and types from the lambda. For promoted
             type vars (e.g., Tvar 3 for edge in Graph), substitute them with
             their concrete types from type_args. Only substitute Tvars beyond
             the ip_sign Keep count to avoid disturbing regular type variable
             references. *)
          let nb_sign_keeps = List.length tv_temps in
          let subst_promoted_tvars ty =
            if List.length type_args > nb_sign_keeps then
              let rec subst = function
                | Miniml.Tvar j
                  when j > nb_sign_keeps && j <= List.length type_args ->
                  List.nth type_args (j - 1)
                | Miniml.Tarr (a, b) -> Miniml.Tarr (subst a, subst b)
                | Miniml.Tglob (r, l, a) -> Miniml.Tglob (r, List.map subst l, a)
                | Miniml.Tmeta {contents = Some t} -> subst t
                | Miniml.Tmeta _ as t -> t
                | t -> t
              in
              subst ty
            else
              ty
          in
          let rec extract_params ml_acc cpp_acc body =
            match body with
            | MLlam (id, ty, rest) ->
              let param_name = id_of_mlid id in
              let resolved_ty = subst_promoted_tvars ty in
              let param_cpp_ty =
                convert_ml_type_to_cpp_type
                  base_env
                  Refset'.empty
                  type_var_names
                  resolved_ty
              in
              extract_params
                ((param_name, resolved_ty) :: ml_acc)
                ((param_name, param_cpp_ty) :: cpp_acc)
                rest
            | _ -> (List.rev ml_acc, List.rev cpp_acc, body)
          in
          let ml_params, cpp_params, inner_body =
            extract_params [] [] field_body
          in
          (* Determine return type: if type_subst resolved everything, use the
             substituted type. Otherwise, infer from the lambda binders. *)
          let method_ret_ty =
            let ret = ml_return_type subst_ty in
            match ret with
            | (Tvar _ | Tvar' _) when ml_params <> [] ->
              (* Unsubstituted Tvar — infer from the last lambda binder's type.
                 For op : A -> A -> A with body MLlam(x, nat, MLlam(y, nat,
                 ...)), the return type is the same as the parameter type
                 (nat). *)
              let last_param_ty = snd (List.hd (List.rev ml_params)) in
              convert_ml_type_to_cpp_type
                base_env
                Refset'.empty
                type_var_names
                last_param_ty
            | Tvar _ | Tvar' _ ->
              (* No lambda binders to infer from — try to use the field type's
                 arg types. For a non-function field like m_id : carrier, the
                 whole type is Tvar, so look at the body's type. *)
              Tany
            | _ ->
              convert_ml_type_to_cpp_type
                base_env
                Refset'.empty
                type_var_names
                ret
          in
          let cpp_params, ret_ty, body_stmts =
            if ml_params = [] then
              (* No lambdas in the body — either a function reference that needs
                 eta-expansion, or a non-function value field. *)
              let arg_types, _ret_type = get_args_and_ret [] subst_ty in
              (* Filter out type class instance args *)
              let arg_types =
                List.filter (fun t -> not (Table.is_typeclass_type t)) arg_types
              in
              if arg_types = [] then
                (* Non-function field (like m_id : carrier) — generate as a
                   static value with a nullary accessor method. *)
                let stmts =
                  gen_stmts base_env (fun x -> Sreturn (Some x)) inner_body
                in
                ([], method_ret_ty, stmts)
              else
                (* Function reference — eta-expand based on the field type's
                   args *)
                let params =
                  List.mapi
                    (fun i arg_ty ->
                      let name = Id.of_string ("a" ^ string_of_int i) in
                      let cpp_ty =
                        convert_ml_type_to_cpp_type
                          base_env
                          Refset'.empty
                          type_var_names
                          arg_ty
                      in
                      (name, arg_ty, cpp_ty) )
                    arg_types
                in
                let nparams = List.length params in
                let ml_rels =
                  List.mapi (fun i _ -> MLrel (nparams - i)) params
                in
                (* Lift the body's de Bruijn indices to account for the new eta
                   params *)
                let lifted_body = Mlutil.ast_lift nparams inner_body in
                let call_expr = MLapp (lifted_body, ml_rels) in
                let ml_vars =
                  List.rev_map (fun (name, ml_ty, _) -> (name, ml_ty)) params
                in
                let renamed_eta, env = push_vars' ml_vars base_env in
                let stmts =
                  gen_stmts env (fun x -> Sreturn (Some x)) call_expr
                in
                (* Sync param names with push_vars' output (lowercased
                   and uniquified) so signatures match bodies.  ml_vars
                   was built via List.rev_map, so renamed_eta is in
                   reversed order — reverse back to align with params. *)
                let cpp_params =
                  List.map2
                    (fun (new_name, _) (_, cpp_ty) -> (new_name, cpp_ty))
                    (List.rev renamed_eta)
                    (List.map (fun (name, _, cpp_ty) -> (name, cpp_ty)) params)
                in
                (cpp_params, method_ret_ty, stmts)
            else
              (* Normal case: we have lambdas.  push_vars' lowercases
                 and uniquifies names for the de Bruijn environment;
                 sync cpp_params so the method signature matches. *)
              let renamed_ml, env =
                push_vars' (List.rev ml_params) base_env
              in
              let cpp_params =
                List.map2
                  (fun (new_name, _) (_, cpp_ty) -> (new_name, cpp_ty))
                  (List.rev renamed_ml)
                  cpp_params
              in
              let stmts =
                gen_stmts env (fun x -> Sreturn (Some x)) inner_body
              in
              (cpp_params, method_ret_ty, stmts)
          in
          Some
            ( Fmethod
                {
                  mf_name = method_name;
                  mf_tparams = [];
                  mf_ret_type = ret_ty;
                  mf_params = cpp_params;
                  mf_body = body_stmts;
                  mf_is_const = false;
                  mf_is_static = true;
                  mf_is_inline = false;
                  mf_this_pos = 0;
                  mf_no_pure = false;
                },
              VPublic,
              SNoTag )
      in
      (* Zip fields with their types from ind_packet *)
      let fields_with_types =
        if List.length fields = List.length field_types then
          List.combine fields field_types
        else (* Fallback: pair fields with Tunknown if lengths don't match *)
          List.map (fun f -> (f, Miniml.Tunknown)) fields
      in
      let method_pairs = List.combine fields_with_types method_bodies in
      let methods =
        List.filter_map
          (fun ((fld, fty), body) -> gen_method (fld, fty) body)
          method_pairs
      in
      (* Generate [using] declarations for promoted typeclass-typed fields
         from the constructor body.  For such fields, the constructor arg
         is a value expression (e.g., [MLglob nat_category] or
         [MLapp(opposite_category, [MLproj(...)])]) that must be
         translated to a C++ TYPE expression (e.g., [nat_category] or
         [opposite_category<typename _tcI0::base_category>]).

         This function interprets an ML expression at the type level:
         - [MLglob r] → named type [Tglob(r, ...)]
         - [MLapp(MLglob r, args)] → template type with type args
         - [MLrel i] → template parameter reference [Tvar(0, Some name)]
         - [MLmagic e] → strip magic wrapper *)
      let rec ml_expr_to_cpp_type body =
        match body with
        | MLglob (r, _) -> Tglob (r, [], [])
        | MLapp (MLglob (r, _), args) ->
          let type_args = List.filter_map ml_expr_to_cpp_type_opt args in
          Tglob (r, type_args, [])
        | MLapp (f, args) -> (
          match ml_expr_to_cpp_type f with
          | Tglob (r, existing, es) ->
            let type_args = List.filter_map ml_expr_to_cpp_type_opt args in
            Tglob (r, existing @ type_args, es)
          | other -> other )
        | MLrel i -> (
          try
            let name = get_db_name i base_env in
            Tvar (0, Some name)
          with Failure _ -> Tany )
        | MLmagic e -> ml_expr_to_cpp_type e
        | MLcase (_, scrutinee, branches)
          when Array.length branches = 1 ->
          (* Single-branch case = record field projection.  The branch
             destructures the record into named bindings and selects one
             via [MLrel].  Translate into [Tqualified(scrutinee, field)]. *)
          let (binds, _, _, br_body) = branches.(0) in
          let base_ty = ml_expr_to_cpp_type scrutinee in
          ( match br_body with
          | MLrel j when j >= 1 && j <= List.length binds ->
            (* de Bruijn: 1 = last binding, n = first binding *)
            let idx = List.length binds - j in
            let (field_id, _) = List.nth binds idx in
            ( match field_id with
            | Id name | Tmp name -> Tqualified (base_ty, name)
            | Dummy -> Tany )
          | _ ->
            (* Non-trivial body — recurse with extended environment *)
            ml_expr_to_cpp_type br_body )
        | _ -> Tany
      and ml_expr_to_cpp_type_opt body =
        match ml_expr_to_cpp_type body with
        | Tany -> None
        | t -> Some t
      in
      (* Check if an ML expression is a parameterized reference whose
         typeclass arguments have been erased — e.g.,
         [MLapp(MLglob opposite_category, [MLdummy Ktype])].  Such
         references produce incomplete [Tglob(r, [], [])] that can't
         be used as using declarations. *)
      let tc_promoted_usings =
        if List.length fields_with_types = List.length method_bodies then
          List.filter_map
            (fun ((fld, fty), body) ->
              match (fld, fty) with
              | Some field_ref, Miniml.Tglob (r, _, _)
                when Table.is_typeclass r ->
                let has_erased_tc_args =
                  match body with
                  | MLapp (_, args) ->
                    List.exists
                      (function MLdummy _ -> true | _ -> false)
                      args
                  | _ -> false
                in
                if has_erased_tc_args then
                  (* Parameterized reference with erased typeclass args.
                     Fall through to let forwarded_usings handle this
                     field. *)
                  None
                else
                  let field_name_str =
                    Common.pp_global_name Term field_ref
                  in
                  let field_id = Id.of_string field_name_str in
                  let cpp_ty = ml_expr_to_cpp_type body in
                  if cpp_ty = Tany then None
                  else
                    Some
                      ( Fnested_using (field_id, cpp_ty),
                        VPublic,
                        SNoTag )
              | _ -> None )
            (List.combine fields_with_types method_bodies)
        else
          []
      in
      (* Restore type variable context *)
      tctx.current_outer_function_name <- saved_outer_name;
      clear_current_type_vars ();
      (* Compute promoted vars and generate using fields. Promoted vars are
         ip_vars entries beyond the real type parameter count (as determined by
         ip_sign Keep count, not tv_temps which reflects the instance's own type
         variables). They become `using field = ConcreteType;` in the struct. *)
      let ip_vars = Table.get_ind_ip_vars class_ref in
      let nb_sign_keeps_for_promoted = Table.get_ind_nb_sign_keeps class_ref in
      let promoted_vars =
        List.filteri (fun i _ -> i >= nb_sign_keeps_for_promoted) ip_vars
      in
      let promoted_concrete_types =
        if List.length type_args > nb_sign_keeps_for_promoted then
          List.filteri (fun i _ -> i >= nb_sign_keeps_for_promoted) type_args
        else
          []
      in
      (* Is [cpp_ty] a self-referential promoted-var reference (e.g.,
         [Tvar(_, Some "Obj")] where "Obj" is a promoted var)?  Such
         types are useless: [using Obj = Obj;] would just alias the
         enclosing scope, not the template parameter's type. *)
      let is_self_referential_promoted var_name cpp_ty =
        match cpp_ty with
        | Tvar (_, Some id) when Id.equal id var_name -> true
        | _ -> false
      in
      (* For each concept-constrained template parameter, forward its
         promoted type aliases into this struct.  E.g., if [_tcI0]
         satisfies [PreCategory] which has promoted [Obj], generate
         [using Obj = typename _tcI0::Obj;]. *)
      let forwarded_usings =
        List.concat_map
          (fun (tt, tc_name) ->
            match tt with
            | TTconcept class_ref_tc ->
              let tc_ip_vars = Table.get_ind_ip_vars class_ref_tc in
              let tc_nb_keeps = Table.get_ind_nb_sign_keeps class_ref_tc in
              let tc_promoted =
                List.filteri (fun i _ -> i >= tc_nb_keeps) tc_ip_vars
              in
              List.map
                (fun var_name ->
                  let qualified_ty =
                    Tqualified (Tvar (0, Some tc_name), var_name)
                  in
                  ( Fnested_using (var_name, qualified_ty),
                    VPublic,
                    SNoTag ) )
                tc_promoted
            | _ -> [] )
          template_params
      in
      (* Collect names already covered by TC-promoted usings (from
         constructor body).  These take priority over forwarded usings
         because they carry the computed type expression rather than
         a simple forward from the template parameter. *)
      let tc_promoted_names =
        List.filter_map
          (fun (f, _, _) ->
            match f with
            | Fnested_using (id, _) -> Some id
            | _ -> None )
          tc_promoted_usings
      in
      (* Remove forwarded usings that are superseded by TC-promoted usings *)
      let forwarded_usings =
        List.filter
          (fun (f, _, _) ->
            match f with
            | Fnested_using (id, _) ->
              not (List.exists (Id.equal id) tc_promoted_names)
            | _ -> true )
          forwarded_usings
      in
      (* Collect names already covered by forwarded usings. *)
      let forwarded_names =
        List.filter_map
          (fun (f, _, _) ->
            match f with
            | Fnested_using (id, _) -> Some id
            | _ -> None )
          forwarded_usings
      in
      (* Generate [using VarName = ConcreteType;] for each promoted
         variable that has a known, non-self-referential concrete type
         and is not already covered by a forwarded using.  Use
         zip-up-to-minimum so that partially-extractable Records
         still get declarations for the extractable promoted vars. *)
      let concrete_usings =
        let n =
          min (List.length promoted_vars) (List.length promoted_concrete_types)
        in
        List.init n (fun i ->
            let var_name = List.nth promoted_vars i in
            let concrete_ml_ty = List.nth promoted_concrete_types i in
            let concrete_cpp_ty =
              convert_ml_type_to_cpp_type
                base_env
                Refset'.empty
                type_var_names
                concrete_ml_ty
            in
            (var_name, concrete_cpp_ty) )
        |> List.filter_map (fun (var_name, concrete_cpp_ty) ->
               if
                 List.exists (Id.equal var_name) tc_promoted_names
                 || List.exists (Id.equal var_name) forwarded_names
                 || is_self_referential_promoted var_name concrete_cpp_ty
               then
                 None
               else
                 Some
                   ( Fnested_using (var_name, concrete_cpp_ty),
                     VPublic,
                     SNoTag ) )
      in
      (* Exclude promoted type args from the returned list (used for
         static_assert) *)
      let non_promoted_type_args =
        List.filteri (fun i _ -> i < nb_sign_keeps_for_promoted) type_args
      in
      (* Generate nested promoted-var usings.  When a using aliases a
         typeclass-typed field (e.g., [using base_category = nat_category;]),
         we must also forward the promoted vars of that typeclass so that
         method return types resolve correctly.  E.g., if [base_category]
         satisfies [PreCategory] with promoted [Obj], generate
         [using Obj = typename base_category::Obj;]. *)
      let direct_usings =
        tc_promoted_usings @ forwarded_usings @ concrete_usings
      in
      let direct_names =
        List.filter_map
          (fun (f, _, _) ->
            match f with Fnested_using (id, _) -> Some id | _ -> None)
          direct_usings
      in
      let nested_promoted_usings =
        List.concat_map
          (fun (f, _, _) ->
            match f with
            | Fnested_using (using_name, _using_ty) ->
              (* Find this field's ML type in the typeclass definition *)
              let field_ml_ty =
                List.find_map
                  (fun (fld_opt, fml_ty) ->
                    match fld_opt with
                    | Some fld_ref ->
                      let fld_name_str =
                        Common.pp_global_name Term fld_ref
                      in
                      if String.equal fld_name_str (Id.to_string using_name)
                      then Some fml_ty
                      else None
                    | None -> None)
                  fields_with_types
              in
              ( match field_ml_ty with
              | Some (Miniml.Tglob (tc_ref, _, _))
                when Table.is_typeclass tc_ref ->
                let nested_ip = Table.get_ind_ip_vars tc_ref in
                let nested_nk = Table.get_ind_nb_sign_keeps tc_ref in
                let nested_promoted =
                  List.filteri (fun i _ -> i >= nested_nk) nested_ip
                in
                List.filter_map
                  (fun v ->
                    if List.exists (Id.equal v) direct_names then None
                    else
                      Some
                        ( Fnested_using
                            ( v,
                              Tqualified
                                (Tvar (0, Some using_name), v) ),
                          VPublic,
                          SNoTag ))
                  nested_promoted
              | _ -> [] )
            | _ -> [])
          direct_usings
      in
      let all_usings = direct_usings @ nested_promoted_usings in
      if methods = [] && all_usings = [] then
        (None, Some class_ref, non_promoted_type_args)
      else
        let decl =
          Dstruct
            {
              ds_ref = name;
              ds_fields = all_usings @ methods;
              ds_tparams = template_params;
              ds_constraint = None;
              ds_needs_shared_from_this = false;
            }
        in
        (Some decl, Some class_ref, non_promoted_type_args)
    | _ -> (None, Some class_ref, type_args) )
  | _ -> (None, None, [])

(** Check if a term is a type class instance (constructs a type class record) *)
let is_typeclass_instance (_body : ml_ast) (ty : ml_type) : bool =
  match ml_return_type ty with
  | Tglob (class_ref, _, _) -> Table.is_typeclass class_ref
  | _ -> false

(** Parse a custom template string to find which [%tN] positions are
    referenced.  Returns the set of 0-based indices that appear in the
    template.  E.g. ["std::shared_ptr<ITree<%t1>>"] returns [{1}]. *)
let template_referenced_positions template_str =
  let len = String.length template_str in
  let rec scan i acc =
    if i > len - 3 then acc
    else if template_str.[i] = '%' && template_str.[i + 1] = 't' then
      let digit_start = i + 2 in
      let rec find_digit_end j =
        if j < len && template_str.[j] >= '0' && template_str.[j] <= '9' then
          find_digit_end (j + 1)
        else j
      in
      let digit_end = find_digit_end digit_start in
      if digit_end > digit_start then
        let idx =
          int_of_string
            (String.sub template_str digit_start (digit_end - digit_start))
        in
        scan digit_end (IntSet.add idx acc)
      else scan (i + 1) acc
    else scan (i + 1) acc
  in
  scan 0 IntSet.empty

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

(** Collect (index, name) pairs for all Tvar occurrences, sorted by index *)
let get_tvars_indexed t =
  let get_name i n =
    match n with
    | None -> tvar_id i
    | Some n -> n
  in
  let rec aux l = function
    | Tvar (1000, _) ->
      (* Promoted type var marker from a Record-turned-TypeClass.  These
         represent projected type members (e.g., [Obj] from [PreCategory])
         and must be resolved through typeclass instance access — not as
         standalone template parameters. *)
      l
    | Tvar (i, n) ->
      if List.exists (fun (x, _) -> i == x) l then
        l
      else
        (i, get_name i n) :: l
    | Tglob (_, tys, _) -> List.fold_left aux l tys
    | Tfun (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Tmod (_, ty) -> aux l ty
    | Tnamespace (_, ty) -> aux l ty
    | Tref ty -> aux l ty
    | Tvariant tys -> List.fold_left aux l tys
    | Tshared_ptr ty -> aux l ty
    | Tunique_ptr ty -> aux l ty
    | _ -> l
  in
  List.sort (fun (x, _) (y, _) -> Int.compare x y) (aux [] t)

(** Like [get_tvar_indices] but only collects tvars that will actually
    appear in the rendered C++ type.  For custom types with a template
    (e.g. [std::shared_ptr<ITree<%t1>>]), only type-arg positions
    referenced by the template are visited.  Unreferenced positions hold
    phantom tvars (e.g. E in [itree E R] where the template only uses
    [%t1] = R) that the C++ compiler cannot deduce. *)
let get_rendered_tvar_indices t =
  let rec aux l = function
    | Tvar (1000, _) -> l
    | Tvar (i, _) ->
      if List.mem i l then l else i :: l
    | Tglob (g, tys, _) ->
      let tys_to_visit =
        match custom_referenced_positions_opt g with
        | Some referenced ->
          List.filteri (fun i _ -> IntSet.mem i referenced) tys
        | None -> tys
      in
      List.fold_left aux l tys_to_visit
    | Tfun (tys, ty) -> List.fold_left aux l (ty :: tys)
    | Tmod (_, ty) -> aux l ty
    | Tnamespace (_, ty) -> aux l ty
    | Tref ty -> aux l ty
    | Tvariant tys -> List.fold_left aux l tys
    | Tshared_ptr ty -> aux l ty
    | Tunique_ptr ty -> aux l ty
    | _ -> l
  in
  aux [] t

(** Tvar names, sorted by index *)
let get_tvars t = List.map snd (get_tvars_indexed t)

(** Tvar indices only (unsorted) *)
let get_tvar_indices t = List.map fst (get_tvars_indexed t)

(** Collect tvar indices that are deducible by the C++ compiler: those appearing
    in the codomain or in non-function-typed domain params. Function-typed
    params are excluded because gen_dfun converts them to auto-deduced Fn&&
    template parameters, hiding their original Rocq-level type variables from
    C++ template argument deduction. Used by both gen_dfun (to decide whether a
    function param should get a MapsTo constraint or plain TTtypename) and
    gen_decl_for_pp (to filter out phantom tvars from the template param list).
*)
let primary_tvar_indices dom cod =
  let non_fun_dom =
    List.filter
      (fun t ->
        match t with
        | Tfun _ -> false
        | _ -> true )
      dom
  in
  List.fold_left
    (fun acc t ->
      List.fold_left (fun a i -> IntSet.add i a) acc
        (get_rendered_tvar_indices t) )
    IntSet.empty
    (cod :: non_fun_dom)

(** Build template parameter list with phantom detection.

    Type variables that appear in the codomain or non-function domain params
    (i.e. {!primary_tvar_indices}) are emitted as plain [typename T].  All
    others — phantom tvars from erased HKT positions or custom-template
    positions that the C++ compiler cannot deduce — are emitted with a
    [void] default ([typename T = void]).

    We never {i remove} tvars from the list: only default them.  Removing
    would shift the de Bruijn index-to-name mapping used throughout the
    pipeline (see {!convert_ml_type_to_cpp_type}). *)
let phantom_aware_temps cty tvars =
  match cty with
  | Tfun (dom, cod) ->
    let tvars_indexed = get_tvars_indexed cty in
    let primary = primary_tvar_indices dom cod in
    List.map
      (fun (i, id) ->
        if IntSet.mem i primary then
          (TTtypename, id)
        else
          (TTtypename_default Tvoid, id) )
      tvars_indexed
  | _ -> List.map (fun id -> (TTtypename, id)) tvars

(** Substitute [CPPglob id] with [repl] in expressions and statements. Uses
    generic AST visitors for structural recursion. *)
let rec glob_subst_expr (id : GlobRef.t) (repl : cpp_expr) (e : cpp_expr) =
  match e with
  | CPPglob (id', _, _) when Environ.QGlobRef.equal Environ.empty_env id id' ->
    repl
  | _ -> map_expr (glob_subst_expr id repl) (glob_subst_stmt id repl) Fun.id e

(** Statement-level case of {!glob_subst_expr}. *)
and glob_subst_stmt (id : GlobRef.t) (repl : cpp_expr) (s : cpp_stmt) =
  map_stmt (glob_subst_expr id repl) (glob_subst_stmt id repl) Fun.id s

(** Substitute [CPPvar id] with [repl] in expressions and statements. Uses
    generic AST visitors for structural recursion. *)
let rec var_subst_expr (id : Id.t) (repl : cpp_expr) (e : cpp_expr) =
  match e with
  | CPPvar id' when Id.equal id id' -> repl
  | _ -> map_expr (var_subst_expr id repl) (var_subst_stmt id repl) Fun.id e

(** Statement-level case of {!var_subst_expr}. *)
and var_subst_stmt (id : Id.t) (repl : cpp_expr) (s : cpp_stmt) =
  map_stmt (var_subst_expr id repl) (var_subst_stmt id repl) Fun.id s

(** Substitute unnamed type variables with named ones based on a variable list.
    This is used when generating methods to replace T1, T2, etc. with the
    struct's template parameter names like A, B, etc. Uses [map_cpp_type] for
    structural recursion on types. *)
let tvar_subst_type (tvars : Id.t list) : cpp_type -> cpp_type =
  map_cpp_type (fun ty ->
    match ty with
    | Tvar (i, None) ->
      (try Tvar (i, Some (List.nth tvars (pred i))) with Failure _ -> ty)
    | _ -> ty )

(** Substitute type variables in expressions and statements. Uses generic AST
    visitors for structural recursion. *)
let rec tvar_subst_expr (tvars : Id.t list) (e : cpp_expr) : cpp_expr =
  map_expr
    (tvar_subst_expr tvars)
    (tvar_subst_stmt tvars)
    (tvar_subst_type tvars)
    e

(** Statement-level case of {!tvar_subst_expr}. *)
and tvar_subst_stmt (tvars : Id.t list) (s : cpp_stmt) : cpp_stmt =
  map_stmt
    (tvar_subst_expr tvars)
    (tvar_subst_stmt tvars)
    (tvar_subst_type tvars)
    s

(** Detect function-typed parameters that are NOT simply forwarded at
   self-recursive call sites.

   Higher-order function parameters are normally emitted as C++ template
   parameters constrained with a [MapsTo] concept, preserving the exact lambda
   type for inlining.  However, when a recursive call passes a *different*
   expression (not the parameter variable itself) for a function-typed parameter,
   each recursion level creates a new template instantiation with a distinct type,
   leading to infinite recursive template instantiation.

   The fix: detect which parameters are not forwarded unchanged at any recursive
   call site.  Those parameters are emitted as [std::function] instead of template
   parameters, since [std::function] is a concrete type that stays the same
   regardless of wrapping.

   Parameters that ARE forwarded unchanged (e.g., a predicate [p] passed as-is in
   [partition_cps p rest (fun ...)]) keep their template parameter status.
   Non-recursive higher-order functions like [tree_rect] are unaffected since they
   have no self-recursive calls. *)
let detect_non_forwarded_params (self_ref : GlobRef.t) (n_params : int)
    (body : ml_ast) : int list =
  detect_non_forwarded_params_generic
    ~is_self_call:(fun _depth -> function
      | MLglob (r, _) -> Environ.QGlobRef.equal Environ.empty_env r self_ref
      | _ -> false )
    n_params body

(** Generate a C++ function definition from an ML function body.

    When the body has fewer lambda binders than the ML type's domain (i.e. it
    is under-applied), missing parameters are eta-expanded by synthesising
    [MLrel] arguments.  [Tdummy]-typed entries in the missing list are skipped:
    they represent erased type parameters (e.g. [A : Type] in
    [apply : forall A, A -> A]) that have no C++ runtime representation.
    Including them would produce a spurious [CPPabort "unreachable"] IIFE as an
    extra argument, causing [std::function] call sites to receive the wrong
    number of arguments.

    @param n     the global reference for the function being defined
    @param b     the ML AST body
    @param cty   the C++ type of the function (decomposed internally into domain
                 and codomain)
    @param ty    the original ML type (used for domain decomposition and type
                 inference)
    @param temps template type parameters *)
let gen_dfun n b cty ty temps =
  let dom, cod =
    match cty with Tfun (d, c) -> (d, c) | t -> ([ Tvoid ], t)
  in
  (* Suppress __attribute__((pure)) for functions whose ML return type is
     monadic — these perform side effects even though the C++ return type
     may look pure after type erasure. *)
  let no_pure = is_monadic_ml_type (ml_codomain ty) || ast_may_throw b in
  (* Determine itree extraction mode from the monad template string.
     Reified mode preserves [itree E R] as [shared_ptr<ITree<R>>]; sequential
     mode erases to [R].  We detect reified by checking whether the monad
     template contains "ITree" (e.g. ["std::shared_ptr<ITree<%t1>>"]).
     Must be set BEFORE void-ification so the mode is available. *)
  let saved_mode = tctx.itree_mode in
  ( match extract_monad_from_codomain ty with
  | Some monad_ref ->
    tctx.itree_mode <-
      (if is_monad_reified monad_ref then Reified else Sequential)
  | None -> () );
  (* Void-ify unit codomain: unit as return type maps to C++ void.
     Check the ML result type (unwrapping monad if present) to determine
     if the function returns unit. Then recursively replace the unit enum
     with Tvoid in the C++ codomain type.
     - Sequential mode: Unit → void directly (the monad wrapper is erased,
       so the C++ function literally returns void)
     - Reified mode: Tglob(itree, [E; Unit]) → Tglob(itree, [E; void])
       (printed as shared_ptr<ITree<void>> via monad template) *)
  let unit_void =
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty)
  in
  let cod = apply_unit_void unit_void (tctx.itree_mode = Reified) cod in
  let rec get_dom l ty =
    match ty with
    | Tarr (t1, t2) -> get_dom (t1 :: l) t2
    | _ -> l
  in
  let mldom = get_dom [] ty in
  (* Limit lambda collection to the number of type arrows. When a type alias
     like [State S A = S -> A * S] is used as a return type, the extraction may
     fully uncurry the body (producing more lambdas than the type has arrows),
     but the type [ty] preserves the alias. We must only collect as many lambdas
     as the type has domain arrows, leaving the rest in the body as returned
     closures (C++ lambdas). *)
  let n_type_dom = List.length mldom in
  let all_ids, inner_b = collect_lams b in
  let ids, b =
    if List.length all_ids > n_type_dom then
      let n_excess = List.length all_ids - n_type_dom in
      let kept_ids = List.skipn n_excess all_ids in
      let excess_ids = safe_firstn n_excess all_ids in
      (kept_ids, named_lams excess_ids inner_b)
    else
      (all_ids, inner_b)
  in
  (* get_missing computes the types for eta-expansion parameters. mldom contains
     domain types in reversed order (innermost type first). ids contains
     explicit lambdas in reversed order (innermost lambda first).

     The explicit lambdas bind the OUTERMOST types (at the END of mldom). The
     missing parameters should have the INNERMOST types (at the START of mldom).

     Example: For type R -> nat -> nat -> nat with body λr. <match>: mldom =
     [nat; nat; R] (innermost nat is first, outermost R is last) ids = [(r, R)]
     (one lambda binding the outermost type R) missing types = [nat; nat] (the
     first 2 elements of mldom)

     The old code consumed from HEAD of both lists, incorrectly pairing the
     innermost type (nat) with the outermost lambda (r), causing eta-expansion
     parameters to get wrong types. *)
  let get_missing d a =
    let n_missing = max 0 (List.length d - List.length a) in
    safe_firstn n_missing d
  in
  let missing_types = get_missing mldom ids in
  let n_miss = List.length missing_types in
  (* Assign names so that _x0 gets the outermost missing type (closest to the
     explicit lambdas) and _x(n-1) gets the innermost (= last source param).
     get_missing returns types innermost-first from mldom, so index i maps to
     name _x(n_miss - 1 - i). The resulting list is already in de Bruijn order
     (innermost first) because mapi iterates innermost-first. *)
  let missing =
    List.mapi (fun i t -> (Id (eta_param_id (n_miss - 1 - i)), t)) missing_types
  in
  (* Unify body lambda parameter types with the function signature types.

     When optimize_fix (mlutil.ml) promotes a polymorphic let-fix into a
     top-level Dfix, the body's lambda parameter types may still contain
     unresolved Tmeta cells left over from extraction. For example:

     Definition local_length {A} (l : list A) : nat := let fix go (xs : list A)
     := ... in go l.

     After optimize_fix, the outer function IS the fixpoint, but the lambda
     parameter type for [xs] still holds the original unresolved meta for A,
     while the function's signature type [ty] correctly has Tvar 1 for A.
     Without unification, convert_ml_type_to_cpp_type maps the unresolved meta
     to Tany (std::any), producing e.g. list<std::any> instead of list<T1>.

     By unifying each body parameter type with the corresponding signature type
     via try_mgu, we resolve the shared Tmeta cells in-place. Because metas are
     mutable references shared across the entire body AST, this single
     unification step also fixes every other occurrence of the same meta inside
     the function body (match annotations, recursive calls, etc.). *)
  let n_missing = List.length missing in
  let sig_types_for_ids =
    List.of_seq (Seq.drop n_missing (List.to_seq mldom))
  in
  let rec unify_param_types body_params sig_types =
    match (body_params, sig_types) with
    | (id, body_ty) :: rest_params, sig_ty :: rest_sig ->
      (try try_mgu body_ty sig_ty with _ -> ());
      (id, body_ty) :: unify_param_types rest_params rest_sig
    | _ -> body_params
  in
  let ids = unify_param_types ids sig_types_for_ids in
  (* Replace Tunknown in body param types with corresponding sig types. This
     handles promoted dependent records where the lambda's type annotation has
     Tunknown for the erased carrier, while the function signature has
     Tglob(m_carrier, []) which can be resolved by
     convert_ml_type_to_cpp_type. *)
  let rec merge_unknown body_ty sig_ty =
    match (body_ty, sig_ty) with
    | Miniml.Tunknown, _ -> sig_ty
    | Miniml.Tglob (r1, ts1, a1), Miniml.Tglob (r2, ts2, _)
      when GlobRef.CanOrd.equal r1 r2 && List.length ts1 = List.length ts2 ->
      Miniml.Tglob (r1, List.map2 merge_unknown ts1 ts2, a1)
    | Miniml.Tarr (t1a, t1b), Miniml.Tarr (t2a, t2b) ->
      Miniml.Tarr (merge_unknown t1a t2a, merge_unknown t1b t2b)
    | _ -> body_ty
  in
  let ids =
    if List.length ids = List.length sig_types_for_ids then
      List.map2
        (fun (id, body_ty) sig_ty -> (id, merge_unknown body_ty sig_ty))
        ids
        sig_types_for_ids
    else
      ids
  in
  (* Replace body lambda types with signature types for env_types tracking, but
     ONLY when the signature type has fewer arrows than the body type. This
     handles type aliases like [State S A = S -> A * S] where expansion adds
     extra arrows. Using signature types in env_types ensures that inner call
     sites can detect over-application and generate chained calls (e.g. f(a)(s')
     instead of f(a, s')). We must NOT replace unconditionally, because that
     would make parameter types in the .cpp definition differ from the .h
     declaration (which uses gen_sfun with expanded types). *)
  let ids =
    if List.length ids = List.length sig_types_for_ids then
      List.map2
        (fun (id, body_ty) sig_ty ->
          if count_ml_arrows body_ty > count_ml_arrows sig_ty then
            (id, sig_ty)
          else
            (id, body_ty) )
        ids
        sig_types_for_ids
    else
      ids
  in
  (* Detect which function-typed parameters are NOT simply forwarded at
     self-recursive call sites.  These are excluded from template-parameter
     promotion below — they keep their [Tmod(TMconst, Tfun(dom, cod))] type
     which prints as [const std::function<R(Args...)>].

     [detect_non_forwarded_params] returns source-order indices (param 0 =
     first Rocq parameter).  We need two index-checking helpers because the
     parameter list [ids] is in de Bruijn order (innermost first = last source
     param first), while [List.rev ids] is in source order:

     Source order (Rocq): p0 p1 p2 indices 0, 1, 2 De Bruijn order (ids): p2 p1
     p0 indices 0, 1, 2

     So non-forwarded source index [i] maps to de Bruijn index [n_ids - 1 - i]. *)
  let non_fwd_param_indices = detect_non_forwarded_params n (List.length ids) b in
  let non_fwd_set = IntSet.of_list non_fwd_param_indices in
  let is_non_fwd_param_source i = IntSet.mem i non_fwd_set in
  let n_ids = List.length ids in
  let is_non_fwd_param_db i = IntSet.mem (n_ids - 1 - i) non_fwd_set in
  let all_params = missing @ ids in
  (* Type class instance parameters become C++ template type parameters. We
     assign unique names (_tcI0, _tcI1, ...) to avoid collision with: - User
     variable names like 'i', 'j', etc. - Other generated names in the same
     scope The original parameter order is preserved for correct de Bruijn
     indexing. *)
  let typeclass_counter = ref 0 in
  let typeclass_temps = ref [] in
  let all_params_for_env =
    List.map
      (fun (ml_id, ty) ->
        if Table.is_typeclass_type ty then (
          let i = !typeclass_counter in
          typeclass_counter := i + 1;
          let instance_name = tc_instance_id i in
          (* Build template param info.  Use [TTconcept] for unary
             concepts (nb_sign_keeps = 0) so the C++ compiler enforces
             concept satisfaction, e.g. [PreCategory _tcI0] instead of
             [typename _tcI0]. Multi-parameter concepts cannot use inline
             syntax because extra type args aren't available at the
             template-param declaration site. *)
          let temp_info =
            match ty with
            | Miniml.Tglob (class_ref, type_args, _) ->
              let type_arg_cpp =
                List.map
                  (fun t ->
                    convert_ml_type_to_cpp_type
                      (empty_env ())
                      Refset'.empty
                      []
                      t )
                  type_args
              in
              let tt =
                let nb_keeps = Table.get_ind_nb_sign_keeps class_ref in
                if nb_keeps = 0 then TTconcept class_ref else TTtypename
              in
              ( tt,
                instance_name,
                Some (class_ref, type_arg_cpp),
                remove_prime_id (id_of_mlid ml_id) )
            | _ ->
              ( TTtypename,
                instance_name,
                None,
                remove_prime_id (id_of_mlid ml_id) )
          in
          typeclass_temps := temp_info :: !typeclass_temps;
          (* Return renamed param for env (use instance_name like 'i' instead of
             original name) *)
          (instance_name, ty) )
        else (* Regular param: keep original name *)
          (remove_prime_id (id_of_mlid ml_id), ty) )
      all_params
  in
  let typeclass_temps = List.rev !typeclass_temps in
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
         Converts to [Tvar(1000, Some "m_carrier")] ← needs resolution

       This map provides the resolution:
         "m_carrier" ↦ Tqualified(Tvar(0, Some "_tcI0"), "m_carrier")
         Which prints as: typename _tcI0::m_carrier

     For nested typeclasses (e.g., PreStableCategory has a base_category : PreCategory),
     promoted vars are doubly qualified:
       "Obj" ↦ typename _tcI0::base_category::Obj

     The map is applied by [resolve_promoted_in_type] to substitute all
     [Tvar(1000, ...)] markers with their qualified forms. *)
  let promoted_var_resolutions =
    List.concat_map (fun (_tt, tc_name, class_info, _) ->
      match class_info with
      | Some (class_ref, _) ->
        let ip_vars = Table.get_ind_ip_vars class_ref in
        let nb_keeps = Table.get_ind_nb_sign_keeps class_ref in
        let promoted = List.filteri (fun i _ -> i >= nb_keeps) ip_vars in
        (* Direct promoted vars: Var → typename _tcI0::Var *)
        let direct =
          List.map (fun var_name ->
            (var_name, Tqualified (Tvar (0, Some tc_name), var_name))
          ) promoted
        in
        (* Nested promoted vars from TC-typed fields:
           Var → typename _tcI0::field::Var *)
        let method_list =
          let fields = Table.get_record_fields class_ref in
          let field_types = Table.record_field_types class_ref in
          let non_dummy =
            filter_value_types field_types
          in
          if List.length fields = List.length non_dummy then
            List.combine fields non_dummy
          else []
        in
        let nested =
          List.concat_map (fun (field_opt, field_ty) ->
            match (field_opt, field_ty) with
            | Some field_ref, Miniml.Tglob (r, _, _)
              when Table.is_typeclass r ->
              let field_name_str = Common.pp_global_name Term field_ref in
              let field_id = Id.of_string field_name_str in
              if List.exists (Id.equal field_id) promoted then
                let n_ip = Table.get_ind_ip_vars r in
                let n_nk = Table.get_ind_nb_sign_keeps r in
                let n_promoted =
                  List.filteri (fun i _ -> i >= n_nk) n_ip
                in
                List.filter_map (fun nested_var ->
                  (* Skip if already directly mapped (direct takes priority) *)
                  if List.exists (Id.equal nested_var) promoted then None
                  else
                    Some (nested_var,
                      Tqualified
                        (Tqualified (Tvar (0, Some tc_name), field_id),
                         nested_var))
                ) n_promoted
              else []
            | _ -> []
          ) method_list
        in
        direct @ nested
      | None -> []
    ) typeclass_temps
  in
  (* Substitute promoted type var markers [Tvar(1000, Some name)] with their
     qualified resolutions throughout a C++ type tree. *)
  let rec resolve_promoted_in_type ty =
    match ty with
    | Tvar (1000, Some name) -> (
      match List.find_opt
              (fun (n, _) -> Id.equal n name)
              promoted_var_resolutions with
      | Some (_, resolved) -> resolved
      | None -> ty )
    | Tglob (r, tys, es) ->
      Tglob (r, List.map resolve_promoted_in_type tys, es)
    | Tfun (doms, cod) ->
      Tfun (List.map resolve_promoted_in_type doms,
            resolve_promoted_in_type cod)
    | Tmod (m, t) -> Tmod (m, resolve_promoted_in_type t)
    | Tref t -> Tref (resolve_promoted_in_type t)
    | Tshared_ptr t -> Tshared_ptr (resolve_promoted_in_type t)
    | Tunique_ptr t -> Tunique_ptr (resolve_promoted_in_type t)
    | Tvariant ts -> Tvariant (List.map resolve_promoted_in_type ts)
    | Tqualified (b, id) -> Tqualified (resolve_promoted_in_type b, id)
    | Tnamespace (r, t) -> Tnamespace (r, resolve_promoted_in_type t)
    | Tid (id, ts) -> Tid (id, List.map resolve_promoted_in_type ts)
    | Tid_external (id, ts) -> Tid_external (id, List.map resolve_promoted_in_type ts)
    | Tptr t -> Tptr (resolve_promoted_in_type t)
    | _ -> ty
  in
  (* Apply promoted var resolution to domain and codomain types *)
  let dom =
    if promoted_var_resolutions <> [] then
      List.map resolve_promoted_in_type dom
    else dom
  in
  let cod =
    if promoted_var_resolutions <> [] then
      resolve_promoted_in_type cod
    else cod
  in
  (* Push params into environment for de Bruijn lookup during body generation.
     collect_lams returns params in reverse order (innermost first), so MLrel 1
     refers to the last param in the list.

     push_vars' may rename parameters to avoid collisions. For example, if Rocq
     has: fun (f : T) (f0 : F) (f : forest) => ... push_vars' renames the
     duplicate 'f' to 'f1', producing: [f; f0; f1]

     We must use these renamed ids (all_ids) for both: 1. The environment (for
     correct de Bruijn lookup in the body) 2. The C++ function signature (so
     parameter names match body references)

     Previously, the code discarded all_ids and used original names for the
     signature, causing mismatches like: void foo(T f, F f0, forest f) { ...
     f1->v() ... } where 'f1' in the body didn't match any parameter name. *)
  let all_ids, env = push_vars' all_params_for_env (empty_env ()) in
  reset_env_types ();
  push_env_types all_ids;
  (* Infer owned/borrowed for each parameter. all_params has n elements in de
     Bruijn order (element 0 = de Bruijn 1 = innermost). infer_owned_params
     returns a bool list in the same order. *)
  let n_params = List.length all_params in
  let owned_flags = Escape.infer_owned_params n_params b in
  (* Zip all_ids with ownership flags. all_ids and all_params have the same
     length (push_vars' preserves length), so owned_flags aligns 1:1. *)
  let all_ids_with_owned =
    List.map2 (fun (id, ty) owned -> (id, ty, owned)) all_ids owned_flags
  in
  (* For function signature, use renamed ids but exclude typeclass, void,
     and skipped-type params (e.g. ReSum instances from the ITree library
     that are not recognized by is_typeclass because ReSum's GlobRef is a
     ConstRef, not an IndRef registered in inductive_kinds). *)
  let ids_with_owned =
    List.filter
      (fun (_, ty, _) ->
        (not (Table.is_typeclass_type ty))
        && not (ml_type_is_void ty)
        && not (is_skipped_ml_type ty) )
      all_ids_with_owned
  in
  (* Convert ML types to C++ types and wrap with const. Owned shared_ptr params:
     pass by value (shared_ptr<T>) Borrowed shared_ptr params: pass by const ref
     (const shared_ptr<T>&) *)
  let ids =
    List.map
      (fun (x, ty, owned) ->
        let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty [] ty in
        let cpp_ty =
          if promoted_var_resolutions <> [] then
            resolve_promoted_in_type cpp_ty
          else cpp_ty
        in
        (* Reify monadic parameter types: itree E R → shared_ptr<ITree<R>> *)
        let cpp_ty = reify_monadic_param_type ty cpp_ty in
        let wrapped = wrap_param_by_ownership ~is_owned:owned cpp_ty in
        (x, wrapped) )
      ids_with_owned
  in
  (* Promote forwarded function-typed parameters to C++ template parameters.

     Function-typed parameters (those with C++ type [Tmod(TMconst, Tfun(...))])
     are normally promoted to template parameters with [MapsTo] concept
     constraints.  This replaces [const std::function<R(Args...)>] with a
     template type variable [F&&], giving the compiler the exact lambda
     type so it can inline the call body — no type-erasure overhead.

     For example, [tree_rect]'s two function parameters become:

       template <MapsTo<T1, unsigned int> F0,
                 MapsTo<T1, shared_ptr<tree>, T1, shared_ptr<tree>, T1> F1>
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

     This loop iterates [List.rev ids] which is in source order,
     so we use [is_non_fwd_param_source] for the guard. *)
  (* Determine which tvars are "primary" — deducible from non-function domain
     params or the return type.  Function-typed params that reference tvars
     outside this set (e.g., erased HKT type variables) get TTtypename (no
     MapsTo constraint) instead of TTfun, to avoid referencing template type
     parameters that were filtered out as phantom by gen_decl_for_pp.
     Similarly, function-typed params containing HKT erasure markers (Tany
     or dummy_type) also get TTtypename, since their type structure has been
     partially erased and a MapsTo constraint would be malformed. *)
  let primary = primary_tvar_indices dom cod in
  let fun_tys =
    List.filter_map
      (fun (x, ty, i) ->
        match ty with
        | Tmod (TMconst, Tfun (fdom, fcod)) when not (is_non_fwd_param_source i) ->
          let fun_idx = get_tvar_indices (Tfun (fdom, fcod)) in
          let has_undeclared =
            List.exists (fun idx -> not (IntSet.mem idx primary)) fun_idx
          in
          if has_undeclared || has_hkt_erasure (Tfun (fdom, fcod)) then
            Some (x, TTtypename, fun_tparam_id i)
          else
            let fcod = if is_cpp_unit_type fcod then Tvoid else fcod in
            Some (x, TTfun (fdom, fcod), fun_tparam_id i)
        | _ -> None )
      (List.mapi (fun i (x, ty) -> (x, ty, i)) (List.rev ids))
  in
  (* Replace the parameter type of promoted (forwarded) function params with the
     template type variable [F&&]. Non-forwarded params are left untouched — they
     keep [Tmod(TMconst, Tfun(dom, cod))] which prints as [const
     std::function<R(Args...)>]. This loop iterates [ids] which is in de Bruijn
     order, so we use [is_non_fwd_param_db] for the guard. *)
  let ids =
    List.mapi
      (fun i (x, ty) ->
        match ty with
        | Tmod (TMconst, Tfun (dom, cod)) when not (is_non_fwd_param_db i) ->
          ( x,
            Tref
              (Tref (Tvar (0, Some (fun_tparam_id (List.length ids - i - 1)))))
          )
        | _ -> (x, ty) )
      ids
  in
  (* TODO: below is needed for lambdas in recursive positions, but is badddddd. *)
  (* let rec_fun_tys = List.map (fun (_,t, _) ->
    match t with
    | TTfun (dom, cod) -> Tref (Tmod (TMconst, Tfun (dom, cod)))
    | _ -> CErrors.anomaly (Pp.str "gen_decl: recursive function type expected to be TTfun")) fun_tys in
  let rec_call = CPPglob (n, List.map (fun (_, id) -> Tvar (0, Some id)) temps @ rec_fun_tys) in *)
  (* Add type class instance template parameters - instance types come first *)
  let typeclass_temps_basic =
    List.map (fun (tt, id, _, _) -> (tt, id)) typeclass_temps
  in
  (* Build recursive call reference with typeclass and type params only.
     Function type params (from fun_tys) are excluded because they should be
     deduced from arguments, not explicitly specified in recursive calls. *)
  let rec_call_temps = typeclass_temps_basic @ temps in
  let rec_call =
    mk_cppglob n (List.map (fun (_, id) -> Tvar (0, Some id)) rec_call_temps)
  in
  (* Combine all template params for function signature. Save the non-typeclass
     type params for Tvar index resolution below. *)
  let regular_temps = temps @ List.map (fun (_, t, n) -> (t, n)) fun_tys in
  let temps = typeclass_temps_basic @ regular_temps in
  (* TODO: Build requires clause for type class constraints
     For now, type class constraints are not enforced at compile time.
     The constraints would use the typeclass_temps info to generate
     requires clauses like: requires Eq<I, T1> *)
  (* let forward_fun_args stmt = List.fold_left (fun s (x, _, fid) ->
    var_subst_stmt x (CPPforward (Tvar (0, Some fid), CPPvar x)) s) stmt fun_tys in *)
  (* Set current type variables for pattern matching lambda generation.
     These are the template parameters that can be used in type annotations.
     Exclude typeclass instance params — they are not ML type variables
     and should not participate in Tvar index resolution. ML Tvar indices
     (Tvar 1, Tvar 2, ...) correspond to regular type params only. *)
  let type_var_ids =
    List.filter_map
      (fun (tt, id) ->
        match tt with
        | TTtypename | TTtypename_default _ -> Some id
        | _ -> None )
      regular_temps
  in
  set_current_type_vars type_var_ids;
  set_current_param_types all_ids;
  (* Activate promoted var resolution for body generation — types like
     [Tvar(1000, Some "Obj")] in type annotations will be resolved to
     qualified access through the typeclass instance chain. *)
  let saved_promoted_var_map = tctx.promoted_var_map in
  tctx.promoted_var_map <- promoted_var_resolutions;
  (* Set the outer function name so inner fixpoints can generate lifted names *)
  let saved_outer_name = tctx.current_outer_function_name in
  tctx.current_outer_function_name <- Some (Common.pp_global_name Term n);
  (* Check if the return type is coinductive - if so, wrap body in lazy thunk *)
  let ml_ret = ml_return_type ty in
  let is_cofix_return = Table.is_coinductive_type ml_ret in
  (* For cofixpoints, wrap the return expression in Type::lazy_([=]() ->
     ret_ty { ... }) *)
  let cofix_wrap x =
    if is_cofix_return then
      let ret_cpp = cod in
      let coind_ref =
        match ml_ret with
        | Miniml.Tglob (r, _, _) -> r
        | _ ->
          CErrors.anomaly
            (Pp.str "gen_decl: cofixpoint return type expected to be Tglob")
      in
      let type_args =
        match ml_ret with
        | Miniml.Tglob (_, args, _) ->
          List.map
            (fun t ->
              convert_ml_type_to_cpp_type env Refset'.empty type_var_ids t )
            args
        | _ -> []
      in
      let lazy_factory =
        CPPqualified
          (mk_cppglob coind_ref type_args, Id.of_string "lazy_")
      in
      let thunk = CPPlambda ([], Some ret_cpp, [Sreturn (Some x)], true) in
      Sreturn (Some (CPPfun_call (lazy_factory, [thunk])))
    else if cod = Tvoid then
      (* void function: execute expression for side effects, then return.
         Some tail expressions (like writeTVar) have side effects that must
         not be discarded. Skip pure expressions (variables, enum values,
         inline-custom literals like std::monostate{}) to avoid dead-code
         warnings. *)
      ( match x with
      | CPPenum_val _ | CPPvar _ | CPPint _ | CPPfloat _ | CPPraw _ ->
        Sreturn None
      | CPPglob (_, _, Some ci) when ci.ci_inline <> None -> Sreturn None
      | _ -> Sblock [Sexpr x; Sreturn None] )
    else
      Sreturn (Some x)
  in
  (* Generate sigma type precondition assertions *)
  let sigma_asserts =
    let assertions = Table.get_sigma_assertions n in
    if assertions = [] then
      []
    else
      let all_id_arr = Array.of_list (List.rev all_ids) in
      (* outermost param first *)
      (* Substitute %0, %1, ... placeholders with actual parameter names *)
      let subst_placeholders template =
        let result = ref template in
        Array.iteri
          (fun i (id, _) ->
            let placeholder = Printf.sprintf "%%%d" i in
            let replacement = Id.to_string id in
            let buf = Buffer.create (String.length !result) in
            let s = !result in
            let len = String.length s in
            let plen = String.length placeholder in
            let j = ref 0 in
            while !j < len do
              if !j <= len - plen && String.sub s !j plen = placeholder then (
                Buffer.add_string buf replacement;
                j := !j + plen )
              else (
                Buffer.add_char buf s.[!j];
                j := !j + 1 )
            done;
            result := Buffer.contents buf )
          all_id_arr;
        !result
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
              let expr_str = subst_placeholders template in
              Some (Sassert (expr_str, Some expr_str))
            | Table.AssertComment comment ->
              Some (Sassert ("true", Some comment)) )
        assertions
  in
  tctx.current_letin_depth <- 0;
  tctx.match_param_counter <- 0;
  tctx.cs_counter <- 0;
  (* Phase 2: Initialize owned-variable tracking for move insertion. Parameters
     at de Bruijn indices 1..n_params; owned ones get added to the set. *)
  let n_all_params = List.length all_params in
  tctx.move_n_params <- n_all_params;
  tctx.move_owned_vars <-
    List.fold_left
      (fun acc (i, owned) ->
        if owned && Escape.is_shared_ptr_type (snd (List.nth all_params i)) then
          Escape.IntSet.add (i + 1) acc
        else
          acc )
      Escape.IntSet.empty
      (List.mapi (fun i o -> (i, o)) owned_flags);
  tctx.move_dead_after <- Escape.IntSet.empty;
  (* Expose the C++ return type to inner call sites so they can recover erased
     template type args (see try_recover_erased_return_type). *)
  let saved_return_type = tctx.current_cpp_return_type in
  tctx.current_cpp_return_type <- Some cod;
  (* For non-inlined custom constants (axioms mapped via Crane Extract
     Constant), generate a forwarding body that delegates to the custom
     implementation instead of the default CPPabort throw. *)
  let custom_forwarding_body =
    match b with
    | MLaxiom _ when is_custom n && not (to_inline n) ->
      let custom_name = find_custom n in
      let param_vars = List.rev_map (fun (id, _) -> CPPvar id) ids in
      Some [Sreturn (Some (CPPfun_call (CPPraw custom_name, param_vars)))]
    | _ -> None
  in
  (* method_self_ns is set by the caller (gen_decl/gen_dfun_def) before
     computing cty, so it's already active here. *)
  let inner =
    if missing == [] then (
      let b =
        match custom_forwarding_body with
        | Some stmts -> stmts
        | None ->
          let b =
            List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap b)
          in
          return_captures_by_value b
      in
      clear_current_type_vars ();
      clear_current_param_types ();
      Dfundef ([(n, [])], cod, ids, sigma_asserts @ b, no_pure) )
    else
      (* Eta-expansion: the body 'b' references original params starting at
         MLrel 1. After adding k=|missing| new params to the environment, the
         original params are now at indices k+1, k+2, etc. We must lift 'b' by k
         to adjust its references.

         Example: For accessor f : R -> nat -> nat -> nat with body λr. match
         r... - Original body references r as MLrel 1 - After adding 2
         eta-params (_x0, _x1), environment is [_x1; _x0; r] - r is now at index
         3, so we lift b by 2: MLrel 1 -> MLrel 3

         Then we apply the lifted body to the eta-expansion arguments.

         Exception: axiom/exn bodies always throw — applying them to arguments
         produces invalid C++ (calling a void result). Generate the body
         directly. *)
      let b =
        match custom_forwarding_body with
        | Some stmts -> stmts
        | None ->
        match b with
        | MLaxiom _ | MLexn _ ->
          List.map (glob_subst_stmt n rec_call) (gen_stmts env cofix_wrap b)
        | _ ->
          let k = List.length missing in
          let lifted_b = ast_lift k b in
          (* Only pass value-typed (non-dummy) eta args to the body.
             Dummy-typed entries in [missing] represent erased type parameters
             (e.g. [A : Type] in [apply : forall A, A -> A]).  Passing
             [MLrel (i+1)] for them would generate a [CPPabort "unreachable"]
             IIFE as an extra argument to a [std::function] field that only
             takes one value argument. *)
          let args = List.rev (List.filter_map
            (fun (i, (_, t)) -> if isTdummy t then None else Some (MLrel (i + 1)))
            (List.mapi (fun i x -> (i, x)) missing)) in
          List.map
            (glob_subst_stmt n rec_call)
            (gen_stmts env cofix_wrap (MLapp (lifted_b, args)))
      in
      let b = return_captures_by_value b in
      (* let b = List.map forward_fun_args b in *)
      clear_current_type_vars ();
      clear_current_param_types ();
      Dfundef ([(n, [])], cod, ids, sigma_asserts @ b, no_pure)
  in
  tctx.current_cpp_return_type <- saved_return_type;
  tctx.current_outer_function_name <- saved_outer_name;
  tctx.promoted_var_map <- saved_promoted_var_map;
  (* {b Entry point detection for monadic [main].}

     When a Rocq definition named [main] has a monadic return type, it is
     treated as the program entry point.  The generated C++ must provide a
     standard [int main()] — the handling depends on two factors:

     {b 1. Inside a struct} ([struct_name = Some _]):
       The function keeps its original name.  [Struct::main()] does not
       collide with the free [int main()] because C++ member functions
       occupy a separate scope.  A wrapper [int main() \{ Struct::main(); \}]
       is generated by {!Extract_env.print_impl_module} from the
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
          let int_ty = Tvar (0, Some (Id.of_string "int")) in
          let rec void_return_to_zero = function
            | Sreturn None -> Sreturn (Some (CPPint 0))
            | Sif (c, t, e) ->
              Sif (c, List.map void_return_to_zero t,
                      List.map void_return_to_zero e)
            | Sblock ss -> Sblock (List.map void_return_to_zero ss)
            | Smatch (branches, default) ->
              Smatch
                ( List.map
                    (fun br ->
                      { br with smb_body = List.map void_return_to_zero br.smb_body })
                    branches,
                  Option.map (List.map void_return_to_zero) default )
            | s -> s
          in
          ( match inner with
          | Dfundef (names, _cod, params, body, flags) ->
            Dfundef (names, int_ty, params, List.map void_return_to_zero body, flags)
          | d -> d )
        | None, true ->
          (* Case 3: top-level reified — rename to [_main], register for
             wrapper that calls [_main()->run()] *)
          let new_label = Label.of_id (Id.of_string "_main") in
          let new_n = GlobRef.ConstRef (Constant.make2 (Constant.modpath c) new_label) in
          Table.set_main_function (Id.of_string "_main") (ml_codomain ty) None needs_run;
          ( match inner with
          | Dfundef (_, cod, params, body, flags) ->
            Dfundef ([(new_n, [])], cod, params, body, flags)
          | d -> d )
      end else
        inner
    | _ -> inner
  in
  (* Restore saved itree mode *)
  tctx.itree_mode <- saved_mode;
  match temps with
  | [] -> (inner, env)
  | l -> (Dtemplate (l, None, inner), env)

(** TODO: is this used? Likely, but the template stuff shouldn't be. *)
let gen_sfun n b dom cod temps =
  let all_params, b = collect_lams b in
  let n_params = List.length all_params in
  let owned_flags = Escape.infer_owned_params n_params b in
  let ids, env =
    push_vars'
      (List.map
         (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
         all_params )
      (empty_env ())
  in
  (* Zip with ownership flags, then filter out void params *)
  let ids_with_owned =
    List.map2 (fun (x, ty) owned -> (x, ty, owned)) ids owned_flags
  in
  let ids_with_owned =
    List.filter (fun (_, ty, _) -> not (ml_type_is_void ty)) ids_with_owned
  in
  (* Convert ML types to C++ types and wrap with const. Owned shared_ptr params:
     pass by value; Borrowed: const ref *)
  let ids =
    List.map
      (fun (x, ty, owned) ->
        let cpp_ty = convert_ml_type_to_cpp_type env Refset'.empty [] ty in
        (* Reify monadic parameter types: itree E R → shared_ptr<ITree<R>> *)
        let cpp_ty = reify_monadic_param_type ty cpp_ty in
        let wrapped = wrap_param_by_ownership ~is_owned:owned cpp_ty in
        (Some x, wrapped) )
      ids_with_owned
  in
  let dom = List.filter (fun ty -> ty != Tvoid) dom in
  (* For already-converted C++ types in dom, wrap shared_ptr with const ref *)
  let args =
    List.mapi
      (fun _i ty ->
        let wrapped = wrap_param_by_ownership ty in
        (None, wrapped) )
      dom
  in
  (* Merge parameter names from [ids] (body lambdas) with resolved types
     from [dom] (function signature).  [ids] carries the correct parameter
     names but may have unresolved promoted type vars (e.g. bare [m_carrier]
     instead of [typename _tcI0::m_carrier]).  [dom] carries fully-resolved
     types from the outer gen_dfun but lacks parameter names.  When lengths
     match, zip names from [ids] with types from [args] to get both. *)
  let params =
    if List.length args = List.length ids then
      List.map2
        (fun (name, _) (_, ty) -> (name, ty))
        ids args
    else if List.length args > List.length ids then
      List.rev args
    else
      ids
  in
  let inner = Dfundecl ([(n, [])], cod, params, false) in
  match temps with
  | [] -> (inner, env)
  | l -> (Dtemplate (l, None, inner), env)

(** Build a map from erased field projection GlobRefs to their Tvar index for a
    promoted dependent record / typeclass. Returns [(GlobRef.t * int) list]
    where int is the 1-based Tvar index. *)
let erased_proj_tvar_map (class_ref : GlobRef.t) : (GlobRef.t * int) list =
  let open GlobRef in
  match class_ref with
  | IndRef (kn, _) | ConstructRef ((kn, _), _) ->
    let promoted_vars = Table.get_ind_ip_vars class_ref in
    if promoted_vars = [] then
      []
    else
      let mp = MutInd.modpath kn in
      let n_promoted = List.length promoted_vars in
      List.mapi
        (fun i var_id ->
          let knp = Constant.make2 mp (Label.of_id var_id) in
          (ConstRef knp, n_promoted - i) )
        promoted_vars
  | _ -> []

(** Expand TC-typed carrier refs to their nested Type-valued promoted vars.

    When a typeclass has a promoted field whose ML type is itself a typeclass
    (e.g., [base_category : PreCategory] in [PreStableCategory]),
    [erased_proj_tvar_map] returns a reference to the TC-typed field (e.g.,
    [ConstRef base_category]).  Using that directly in [rewrite_ml_ast_types]
    produces the wrong C++ type — [typename _tcI0::base_category] instead of
    [typename _tcI0::base_category::Obj].

    This function replaces TC-typed carrier refs with the Type-valued promoted
    vars of the nested typeclass.  Expansion is recursive: if the nested TC
    itself has TC-typed promoted vars, they are expanded further.

    @param class_ref  The containing typeclass (e.g., [PreStableCategory])
    @param carrier_refs  The list from [erased_proj_tvar_map] *)
let rec expand_tc_typed_carriers
    (class_ref : GlobRef.t)
    (carrier_refs : (GlobRef.t * int) list)
    : (GlobRef.t * int) list =
  let fields = Table.get_record_fields class_ref in
  let field_types = Table.record_field_types class_ref in
  let non_dummy =
    filter_value_types field_types
  in
  if List.length fields <> List.length non_dummy then
    carrier_refs
  else
    let field_type_pairs = List.combine fields non_dummy in
    let expanded =
      List.concat_map (fun (ref, idx) ->
        let ref_name = Common.pp_global_name Common.Term ref in
        match List.find_opt (fun (fopt, _) ->
          match fopt with
          | Some fr -> Common.pp_global_name Common.Term fr = ref_name
          | None -> false
        ) field_type_pairs with
        | Some (_, Miniml.Tglob (r, _, _)) when Table.is_typeclass r ->
          (* TC-typed carrier — expand to the nested TC's promoted vars *)
          let nested = erased_proj_tvar_map r in
          if nested = [] then [(ref, idx)]
          else expand_tc_typed_carriers r nested
        | _ -> [(ref, idx)]
      ) carrier_refs
    in
    (* Sort by ascending tvar index so the first-declared field (lowest
       index) comes first.  [erased_proj_tvar_map] assigns index
       [n_promoted - i], so field 0 gets index 1 (lowest).  This matters
       because [rewrite_ml_ast_types] uses [List.hd] to pick the carrier. *)
    List.sort (fun (_, i1) (_, i2) -> compare i1 i2) expanded

(** Replace Tglob references to erased projections with Tvar' in an ML type. *)
let rec replace_erased_proj_refs
    (proj_map : (GlobRef.t * int) list)
    (t : ml_type) : ml_type =
  let find_in_map r =
    List.find_map
      (fun (ref, idx) -> if GlobRef.CanOrd.equal r ref then Some idx else None)
      proj_map
  in
  match t with
  | Miniml.Tglob (r, ts, args) ->
    ( match find_in_map r with
    | Some idx -> Miniml.Tvar' idx
    | None ->
      let ts' = List.map (replace_erased_proj_refs proj_map) ts in
      if ts == ts' then t else Miniml.Tglob (r, ts', args) )
  | Miniml.Tarr (t1, t2) ->
    let t1' = replace_erased_proj_refs proj_map t1 in
    let t2' = replace_erased_proj_refs proj_map t2 in
    if t1 == t1' && t2 == t2' then t else Miniml.Tarr (t1', t2')
  | Miniml.Tunknown -> Miniml.Tvar' 1
  | _ -> t

(** Replace Tunknown in all type annotations within an ML AST body with the
    GlobRef of the first promoted type var (the carrier). This allows
    convert_ml_type_to_cpp_type to detect it as a promoted type var.
    [carrier_refs] is a list of (GlobRef.t * int) from erased_proj_tvar_map. *)
let rec rewrite_ml_ast_types
    (carrier_refs : (GlobRef.t * int) list)
    (ast : ml_ast) : ml_ast =
  if carrier_refs = [] then
    ast
  else
    let carrier_ref = fst (List.hd carrier_refs) in
    let rec rty t =
      match t with
      | Miniml.Tunknown -> Miniml.Tglob (carrier_ref, [], [])
      | Miniml.Tmeta ({contents = Some inner} as meta) ->
        let inner' = rty inner in
        if inner != inner' then meta.contents <- Some inner';
        t
      | Miniml.Tmeta ({contents = None} as meta) ->
        (* Unresolved meta — resolve to carrier *)
        meta.contents <- Some (Miniml.Tglob (carrier_ref, [], []));
        t
      | Miniml.Tarr (t1, t2) -> Miniml.Tarr (rty t1, rty t2)
      | Miniml.Tglob (r, ts, a) ->
        let ts' = List.map rty ts in
        Miniml.Tglob (r, ts', a)
      | _ -> t
    in
    let rast = rewrite_ml_ast_types carrier_refs in
    match ast with
    | MLlam (id, ty, body) -> MLlam (id, rty ty, rast body)
    | MLletin (id, ty, e1, e2) -> MLletin (id, rty ty, rast e1, rast e2)
    | MLglob (r, tys) -> MLglob (r, List.map rty tys)
    | MLcons (ty, r, args) -> MLcons (rty ty, r, List.map rast args)
    | MLtuple es -> MLtuple (List.map rast es)
    | MLcase (ty, scrut, branches) ->
      let branches' =
        Array.map
          (fun (binds, bty, pat, body) ->
            let binds' = List.map (fun (id, t) -> (id, rty t)) binds in
            (binds', rty bty, pat, rast body) )
          branches
      in
      MLcase (rty ty, rast scrut, branches')
    | MLfix (i, name_types, bodies, is_cofix) ->
      let name_types' = Array.map (fun (id, ty) -> (id, rty ty)) name_types in
      let bodies' = Array.map rast bodies in
      MLfix (i, name_types', bodies', is_cofix)
    | MLapp (f, args) -> MLapp (rast f, List.map rast args)
    | MLmagic e -> MLmagic (rast e)
    | MLrel _
     |MLdummy _
     |MLaxiom _
     |MLexn _
     |MLuint _
     |MLfloat _
     |MLparray _
     |MLstring _ -> ast

(** Rewrite projection types for promoted dependent records. When a function's
    first parameter is a promoted typeclass (e.g., Magma), and the remaining
    args/return have erased carrier refs, replace them with Tvar references from
    the typeclass's field types.

    The function name [n] is used to find which field of the typeclass this
    projection corresponds to. *)
let rewrite_typeclass_projection_type (n : GlobRef.t) (ty : ml_type) : ml_type =
  match ty with
  | Tarr ((Tglob (class_ref, _, _) as tc_arg), rest)
    when Table.is_typeclass class_ref ->
    let fields = Table.get_record_fields class_ref in
    let field_types = Table.record_field_types class_ref in
    let proj_map = erased_proj_tvar_map class_ref in
    if proj_map <> [] then (* Check if n is a projection of this typeclass *)
      let non_dummy_types =
        filter_value_types field_types
      in
      let non_dummy_fields_types =
        if List.length fields = List.length non_dummy_types then
          List.combine fields non_dummy_types
        else
          List.map (fun f -> (f, Miniml.Tunknown)) fields
      in
      let proj_name = Common.pp_global_name Term n in
      let matching_field_type =
        List.find_map
          (fun (field_ref_opt, ft) ->
            match field_ref_opt with
            | Some fr when Common.pp_global_name Term fr = proj_name -> Some ft
            | _ -> None )
          non_dummy_fields_types
      in
      match matching_field_type with
      | Some field_ty -> Tarr (tc_arg, field_ty)
      | None -> Tarr (tc_arg, replace_erased_proj_refs proj_map rest)
    else
      ty
  | _ -> ty

(** Get the erased projection map for a function's type, if it takes a promoted
    typeclass as first argument. *)
let get_erased_proj_map_from_type (ty : ml_type) : (GlobRef.t * int) list =
  match ty with
  | Tarr (Tglob (class_ref, _, _), _) when Table.is_typeclass class_ref ->
    erased_proj_tvar_map class_ref
  | _ -> []

(** Set method_self_ns from local_inductives for standalone functions.
    Functions inside wrapper modules (e.g. Cotree.tree_of_cotree) construct
    containers whose type parameters must use shared_ptr for recursive
    value-type inductives, matching struct field types.  Returns the saved
    previous value for restoration. *)
let set_method_ns_for_locals () =
  let saved = tctx.method_self_ns in
  let full_ns =
    List.fold_left
      (fun acc g ->
        if Table.has_recursive_fields g && not (is_enum_inductive g)
        then Refset'.add g acc
        else acc)
      tctx.method_self_ns
      (get_local_inductives ())
  in
  tctx.method_self_ns <- full_ns;
  saved

(** Restore method_self_ns to a previously saved value. *)
let restore_method_self_ns saved =
  tctx.method_self_ns <- saved

(** Generate C++ declaration from ML definition (main entry point) *)
let gen_decl n b ty =
  (* Set itree extraction mode early — before type conversion — so that
     reify_monadic_param_type (called inside convert_ml_type_to_cpp_type)
     can correctly voidify unit result types in ITree parameters. *)
  let saved_mode = tctx.itree_mode in
  ( match extract_monad_from_codomain ty with
  | Some monad_ref ->
    tctx.itree_mode <-
      (if is_monad_reified monad_ref then Reified else Sequential)
  | None -> () );
  let saved_method_ns = set_method_ns_for_locals () in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars cty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  let result =
    match cty with
    | Tfun _ ->
      let f, env = gen_dfun n b cty ty temps in
      (f, env, tvars)
    | _ ->
    match b with
    | MLaxiom _ ->
      (* Axiom values become zero-arg functions that throw std::logic_error when
         called. This avoids throwing during static initialization (which
         terminates the program before main). *)
      let body_expr = gen_expr (empty_env ()) b in
      let inner = Dfundef ([(n, [])], cty, [], [Sreturn (Some body_expr)], false) in
      ( match temps with
      | [] -> (inner, empty_env (), tvars)
      | l -> (Dtemplate (l, None, inner), empty_env (), tvars) )
    | _ ->
      let saved_return_type = tctx.current_cpp_return_type in
      tctx.current_cpp_return_type <- Some cty;
      tctx.cs_counter <- 0;
      let body_expr = gen_expr (empty_env ()) b in
      tctx.current_cpp_return_type <- saved_return_type;
      (* When a unit-typed constant's body calls a void-ified function,
         the call produces no value.  Wrap in an IIFE that executes the
         body for side effects and returns Unit::e_TT. *)
      let body_expr =
        if is_cpp_unit_type cty then
          match body_expr with
          | CPPenum_val _ -> body_expr  (* already a literal *)
          | CPPglob (_, _, Some ci) when ci.ci_inline <> None ->
            body_expr  (* inline custom literal (e.g. std::monostate{}) *)
          | _ ->
            CPPfun_call (
              CPPlambda ([], None,
                [Sexpr body_expr; Sreturn (Some (mk_tt_expr ()))],
                false),
              [])
        else body_expr
      in
      let inner = Dasgn (n, cty, body_expr) in
      ( match temps with
      | [] -> (inner, empty_env (), tvars)
      | l -> (Dtemplate (l, None, inner), empty_env (), tvars) )
  in
  tctx.method_self_ns <- saved_method_ns;
  tctx.itree_mode <- saved_mode;
  result

(** Generate C++ declaration with pretty-printing adjustments *)
let gen_decl_for_pp n b ty =
  let carrier_refs = get_erased_proj_map_from_type ty in
  (* Expand TC-typed carrier refs: when a carrier ref points to a
     typeclass-typed promoted field (e.g., base_category : PreCategory),
     replace it with the nested TC's Type-valued promoted vars (e.g., Obj).
     This ensures rewrite_ml_ast_types replaces Tunknown with the actual
     type-level field rather than the struct-level typeclass field. *)
  let carrier_refs =
    match ty with
    | Miniml.Tarr (Miniml.Tglob (class_ref, _, _), _)
      when Table.is_typeclass class_ref ->
      expand_tc_typed_carriers class_ref carrier_refs
    | _ -> carrier_refs
  in
  let b = rewrite_ml_ast_types carrier_refs b in
  let saved_method_ns = set_method_ns_for_locals () in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars cty in
  (* Count typeclass-typed parameters in the ML domain — these become template
     params inside gen_dfun but aren't reflected in tvars (which comes from the
     C++ type). We need tvars to be non-empty when typeclass params exist so
     callers use the full Dtemplate definition. *)
  let tc_param_ids =
    match ty with
    | Tarr _ -> collect_typeclass_param_ids ty
    | _ -> []
  in
  let temps = phantom_aware_temps cty tvars in
  let result = match cty with
  | Tfun (dom, _) ->
    let f, e = gen_dfun n b cty ty temps in
    let fun_tys =
      List.filter_map
        (fun (ty, i) ->
          match ty with
          | Tfun _ -> Some (fun_tparam_id i)
          | _ -> None )
        (List.mapi (fun i ty -> (ty, i)) dom)
    in
    let tvars = tc_param_ids @ tvars @ fun_tys in
    (Some f, e, tvars)
  | _ ->
  match b with
  | MLaxiom _ ->
    (* Axiom values: generate as zero-arg function so they throw when called,
       not at static init time *)
    let body_expr = gen_expr (empty_env ()) b in
    let inner = Dfundef ([(n, [])], cty, [], [Sreturn (Some body_expr)], false) in
    let ds =
      match temps with
      | [] -> inner
      | l -> Dtemplate (l, None, inner)
    in
    (Some ds, empty_env (), tc_param_ids @ tvars)
  | _ -> (None, empty_env (), tc_param_ids @ tvars)
  in
  tctx.method_self_ns <- saved_method_ns;
  result

(** Generate a full C++ function definition for a [Dfix] member.

    Simplifies the ML type, resolves promoted carrier references in the body,
    converts to C++ types, and delegates to {!gen_dfun} for the actual
    definition.  Returns [(decl, env, tvars)]. *)
let gen_dfun_def n b ty =
  (* Simplify the ML type to resolve metavariables before converting to C++ *)
  let ty = type_simpl ty in
  (* Rewrite Tunknown in body types to promoted carrier refs. This allows
     convert_ml_type_to_cpp_type to resolve them correctly. *)
  let carrier_refs = get_erased_proj_map_from_type ty in
  let b = rewrite_ml_ast_types carrier_refs b in
  let b = resolve_body_tvars b ty in
  let saved_method_ns = set_method_ns_for_locals () in
  let cty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars cty in
  let temps = phantom_aware_temps cty tvars in
  (* Count typeclass-typed parameters in the ML domain — these become template
     params inside gen_dfun but aren't reflected in tvars (which comes from the
     C++ type). We need tvars to be non-empty when typeclass params exist so
     callers (gen_dfuns_header) use the full Dtemplate definition. *)
  let tc_param_ids =
    match ty with
    | Tarr _ -> collect_typeclass_param_ids ty
    | _ -> []
  in
  match cty with
  | Tfun (dom, _) ->
    let f, env = gen_dfun n b cty ty temps in
    let fun_tys =
      List.filter_map
        (fun (ty, i) ->
          match ty with
          | Tfun _ -> Some (fun_tparam_id i)
          | _ -> None )
        (List.mapi (fun i ty -> (ty, i)) dom)
    in
    let tvars = tc_param_ids @ tvars @ fun_tys in
    tctx.method_self_ns <- saved_method_ns;
    (f, env, tvars)
  | _ ->
    let f, env = gen_dfun n b cty ty temps in
    tctx.method_self_ns <- saved_method_ns;
    (f, env, tc_param_ids @ tvars)

(** Generate C++ function specification (for header files) *)
let gen_spec n b ty =
  let ty = type_simpl ty in
  let ml_ty = ty in  (* preserve ML type before C++ conversion *)
  let unit_void =
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty) in
  let is_reified = unit_void &&
    (match extract_monad_from_codomain ty with
     | Some mr -> is_monad_reified mr | None -> false) in
  let saved_method_ns = set_method_ns_for_locals () in
  let ty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars ty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  let result =
    match ty with
    | Tfun (dom, cod) ->
      let cod = apply_unit_void unit_void is_reified cod in
      gen_sfun n b dom cod temps
    | _ ->
    match b with
    | MLaxiom _ ->
      (* Axiom values: generate as zero-arg function declaration *)
      let inner = Dfundef ([(n, [])], ty, [], [], false) in
      ( match temps with
      | [] -> (inner, empty_env ())
      | l -> (Dtemplate (l, None, inner), empty_env ()) )
    | _ ->
      (* Expose the constant's C++ type so that inner call sites can recover
         erased template type args (see try_recover_erased_return_type). Without
         this, calls like pick<natBoxed>() inside a constant body cannot deduce
         the missing type parameter. *)
      let saved_return_type = tctx.current_cpp_return_type in
      tctx.current_cpp_return_type <- Some ty;
      (* Strip MLmagic wrapper and track whether a type coercion from std::any
         is needed.  MLmagic wraps expressions when the extraction detects a
         type mismatch (e.g. Obj = std::any vs nat = unsigned int). *)
      let has_magic, inner_body =
        match b with
        | MLmagic inner -> (true, inner)
        | _ -> (false, b)
      in
      (* The optimization pass (simpl) transforms MLmagic(MLapp(f, args)) into
         MLapp(MLmagic(f), args), pushing the magic inside the application head.
         Detect this so we still insert std::any_cast for the result. *)
      let has_magic =
        has_magic || ml_head_has_magic b
      in
      tctx.cs_counter <- 0;
      let b_expr = gen_expr (empty_env ()) inner_body in
      tctx.current_cpp_return_type <- saved_return_type;
      (* Wrap with std::any_cast when the C++ expression returns std::any but the
         declared type is concrete.  Two detection paths:
         (a) MLmagic — the extraction explicitly flagged a type coercion.
         (b) Record field projection — the field's return type is a promoted
             type var (erased to std::any) but Coq's type system sees the
             concrete type, so no MLmagic is generated. *)
      let is_concrete_target =
        match ty with
        | Tany | Tvar _ | Tunknown | Tvoid | Ttodo | Tauto -> false
        | _ -> true
      in
      let needs_any_cast =
        is_concrete_target
        && (has_magic || ml_body_returns_erased_field inner_body)
      in
      let b_expr =
        if needs_any_cast then CPPany_cast (ty, b_expr) else b_expr
      in
      (* When a unit-typed constant's body may call a void-ified function,
         wrap in an IIFE that executes the body for side effects and
         returns Unit::e_TT.  Pure enum literals need no wrapping. *)
      let b_expr =
        if is_cpp_unit_type ty && ml_type_is_unit ml_ty then
          match b_expr with
          | CPPenum_val _ -> b_expr
          | CPPglob (_, _, Some ci) when ci.ci_inline <> None -> b_expr
          | _ ->
            CPPfun_call (
              CPPlambda ([], None,
                [Sexpr b_expr; Sreturn (Some (mk_tt_expr ()))],
                false),
              [])
        else b_expr
      in
      let inner = Dasgn (n, Tmod (TMconst, ty), b_expr) in
      ( match temps with
      | [] -> (inner, empty_env ())
      | l -> (Dtemplate (l, None, inner), empty_env ()) )
  in
  tctx.method_self_ns <- saved_method_ns;
  result

(** Generate a C++ forward declaration (spec) for a struct-level function.

    Produces a simpler signature than {!gen_dfun_def} — suitable for use in
    struct bodies where the full definition is not needed. *)
let gen_sfun_spec n b ty =
  let ty = type_simpl ty in
  let unit_void =
    (match ty with Miniml.Tarr _ -> true
     | Miniml.Tglob (r, _, _) when Table.is_monad r -> true | _ -> false)
    && ml_type_is_unit (ml_result_type ty) in
  let is_reified = unit_void &&
    (match extract_monad_from_codomain ty with
     | Some mr -> is_monad_reified mr | None -> false) in
  let ty = convert_ml_type_to_cpp_type (empty_env ()) Refset'.empty [] ty in
  let tvars = get_tvars ty in
  let temps = List.map (fun id -> (TTtypename, id)) tvars in
  match ty with
  | Tfun (dom, cod) ->
    let cod = apply_unit_void unit_void is_reified cod in
    gen_sfun n b dom cod temps
  | _ ->
    let ty = apply_unit_void unit_void is_reified ty in
    gen_sfun n b [Tvoid] ty temps

(** Generate multiple function definitions *)
let gen_dfuns (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let result = gen_dfun_def name bs.(i) tys.(i) in
      (* Discard lifted declarations here - they are template functions that
         belong only in the header file (.h), not the source file (.cpp).
         gen_dfuns_header will collect them for the header. *)
      ignore (take_lifted_decls ());
      [result] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Convert a Dfundef (definition with body) to a Dfundecl (declaration without
    body). Recursively handles Dtemplate wrappers. Used to generate forward
    declarations that match the full definition's signature (including concept
    constraints). *)
let rec decl_to_spec (d : cpp_decl) : cpp_decl =
  match d with
  | Dfundef (ids, ret_ty, params, body, no_pure) ->
    let no_pure = no_pure ||
      match body with
      | [Sreturn (Some (CPPabort _))] -> true
      | _ -> false
    in
    Dfundecl
      (ids, ret_ty, List.map (fun (id, ty) -> (Some id, ty)) params, no_pure)
  | Dtemplate (temps, cstr, inner) -> Dtemplate (temps, cstr, decl_to_spec inner)
  | _ -> d (* Already a declaration, return as-is *)

(** Generate function declarations for header files *)
let gen_dfuns_header (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let ds, env, tvars = gen_dfun_def name bs.(i) tys.(i) in
      let lifted = take_lifted_decls () in
      let lifted_results = List.map (fun d -> (d, empty_env ())) lifted in
      (* For non-template functions, derive the spec from the definition via
         decl_to_spec to ensure parameter types (owned vs borrowed) match
         exactly between the forward declaration and the out-of-line definition.
         Previously used gen_sfun_spec which ran independent escape
         analysis and could produce different ownership decisions. *)
      let main_result =
        match tvars with
        | [] -> (decl_to_spec ds, env)
        | _ :: _ -> (ds, env)
      in
      lifted_results @ [main_result] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Generate forward declarations (specs) for a group of mutually recursive
    functions, using the SAME signature as the full definitions. This ensures
    the specs match the out-of-line definitions (including concept-constrained
    template parameters). Unlike gen_dfuns_header which may use
    gen_sfun_spec (producing simpler signatures), this always derives the
    spec from gen_dfun_def. *)
let gen_dfuns_spec (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let ds, _env, _tvars = gen_dfun_def name bs.(i) tys.(i) in
      ignore (take_lifted_decls ());
      [(decl_to_spec ds, empty_env ())] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Generate both spec and def for a group of mutually recursive functions in
    one pass. Calls gen_dfun_def ONCE per function, then derives:
    - spec: decl_to_spec of the full definition (forward declaration)
    - def: the full definition (for templates) or None (for non-templates in
      header mode) Returns list of (spec, def_option, lifted_decls) *)
let gen_dfuns_dual ~is_header (ns, bs, tys) =
  List.concat_map
    (fun (i, name) ->
      let ds, env, tvars = gen_dfun_def name bs.(i) tys.(i) in
      let lifted = take_lifted_decls () in
      let spec = (decl_to_spec ds, env) in
      let def =
        match (tvars, is_header) with
        | _ :: _, true -> Some (ds, env) (* Template + header: full def in .h *)
        | _ :: _, false -> None (* Template + source: already in .h *)
        | [], true -> None (* Non-template + header: def goes in .cpp *)
        | [], false -> Some (ds, env)
        (* Non-template + source: full def in .cpp *)
      in
      [(spec, def, lifted)] )
    (List.mapi (fun i name -> (i, name)) (Array.to_list ns))

(** Generate both spec and def for a single Dterm function in one pass. Calls
    gen_decl_for_pp ONCE, then derives both spec and def. Returns (spec_opt,
    def_opt, tvars) *)
let gen_decl_for_pp_dual ~is_header n b ty =
  let ds_opt, env, tvars = gen_decl_for_pp n b ty in
  match (ds_opt, tvars) with
  | Some ds, _ :: _ ->
    (* Template function: spec is decl_to_spec, def only in header *)
    let def = if is_header then Some (ds, env) else None in
    (Some (decl_to_spec ds, env), def, tvars)
  | Some ds, [] ->
    (* Non-template function: spec via decl_to_spec to ensure parameter types
       (owned vs borrowed) match exactly between declaration and definition.
       Using gen_spec here would run independent escape analysis that may
       produce different ownership decisions than gen_dfun used for the def. *)
    let def = if is_header then None else Some (ds, env) in
    (Some (decl_to_spec ds, env), def, tvars)
  | None, _ ->
    (* Non-function type: no def needed *)
    let spec_ds, spec_env = gen_spec n b ty in
    (Some (spec_ds, spec_env), None, tvars)

(** Generate C++ struct for an inductive type (old version).
    @param consarg_names  binder names from {!Miniml.ml_ind_packet.ip_consarg_names};
      when provided, struct fields use descriptive names instead of [d_aJ]. *)
let gen_ind_header ?(consarg_names = [||]) vars name cnames tys =
  let templates = List.map (fun n -> (TTtypename, n)) vars in
  let add_templates d =
    match templates with
    | [] -> d
    | _ -> Dtemplate (templates, None, d)
  in
  let header =
    Array.to_list (Array.map (fun x -> add_templates (Dstruct_decl x)) cnames)
  in
  let vartydecl =
    add_templates
      (Dusing
         ( name,
           Tvariant
             (Array.to_list
                (Array.map
                   (fun x ->
                     Tglob
                       (x, List.mapi (fun i id -> Tvar (i, Some id)) vars, []) )
                   cnames ) ) ) )
  in
  let constrdecl =
    Array.to_list
      (Array.mapi
         (fun i tys ->
           let c = cnames.(i) in
           let ctor_struct_name = ctor_struct_name_of_ref ~fallback_idx:i c in
           let ctor_consarg_names =
             if i < Array.length consarg_names then consarg_names.(i)
             else []
           in
           let n_fields = List.length tys in
           let field_ids =
             compute_and_register_field_names
               ctor_struct_name ctor_consarg_names n_fields
           in
           let constr =
             List.mapi
               (fun i x ->
                 ( List.nth field_ids i,
                   convert_ml_type_to_cpp_type
                     (empty_env ())
                     (Refset'.add name Refset'.empty)
                     vars
                     x ) )
               tys
           in
           (* For function parameters, use const ref for shared_ptr types *)
           let constr_params =
             List.map
               (fun (x, ty) ->
                 let wrapped =
                   match ty with
                   | Tshared_ptr _ | Tunique_ptr _ ->
                     Tref (Tmod (TMconst, ty)) (* const std::shared_ptr<T>& *)
                   | _ -> ty
                 in
                 (x, wrapped) )
               constr
           in
           let make_args =
             List.map
               (fun (x, _) -> mk_cppglob_local (GlobRef.VarRef x) [])
               constr
           in
           let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in
           let make_decl =
             Ffundecl
               ( Id.of_string "make",
                 Tmod (TMstatic, ind_ty_ptr name ty_vars),
                 List.rev constr_params )
           in
           let make_def =
             Ffundef
               ( Id.of_string "make",
                 Tmod (TMstatic, Tshared_ptr (Tglob (name, ty_vars, []))),
                 constr_params,
                 [
                   Sreturn
                     (Some
                        (CPPfun_call
                           ( CPPmk_shared (Tglob (name, ty_vars, [])),
                             [CPPstruct (c, ty_vars, make_args)] ) ) );
                 ] )
           in
           let fields =
             if ty_vars == [] then
               List.append
                 (List.map
                    (fun (x, y) -> (Fvar (x, y), VPublic, SNoTag))
                    constr )
                 [(make_decl, VPublic, SNoTag)]
             else
               List.append
                 (List.map
                    (fun (x, y) -> (Fvar (x, y), VPublic, SNoTag))
                    constr )
                 [(make_def, VPublic, SNoTag)]
           in
           Dstruct
             {
               ds_ref = c;
               ds_fields = fields;
               ds_tparams = templates;
               ds_constraint = None;
               ds_needs_shared_from_this = false;
             } )
         tys )
  in
  Dnspace (Some name, List.append (List.append header [vartydecl]) constrdecl)

(** Replace [Sreturn (Some CPPthis)] with
    [Sreturn (Some (CPPshared_from_this inner_ty))] in method bodies, including
    inside lambdas (e.g., std::visit branches). When a method returns [this]
    directly, the generated C++ would produce [return this;] which fails because
    [this] is a raw pointer but the return type is [std::shared_ptr<T>]. Using
    [shared_from_this()] with [const_pointer_cast] produces a valid [shared_ptr]
    from the raw pointer. *)
let rec replace_return_this_expr inner_ty = function
  | CPPthis -> CPPshared_from_this inner_ty
  | CPPlambda (params, ret, body, cap) ->
    CPPlambda
      (params, ret, List.map (replace_return_this_stmt inner_ty) body, cap)
  | CPPfun_call (f, args) ->
    CPPfun_call
      ( replace_return_this_expr inner_ty f,
        List.map (replace_return_this_expr inner_ty) args )
  | CPPoverloaded exprs ->
    CPPoverloaded (List.map (replace_return_this_expr inner_ty) exprs)
  | e -> e

(** Statement-level counterpart of {!replace_return_this_expr}: recurses into
    if/switch/match branches to replace [return this] with [shared_from_this]. *)
and replace_return_this_stmt inner_ty = function
  | Sreturn (Some e) -> Sreturn (Some (replace_return_this_expr inner_ty e))
  | Sif (cond, then_stmts, else_stmts) ->
    Sif
      ( cond,
        List.map (replace_return_this_stmt inner_ty) then_stmts,
        List.map (replace_return_this_stmt inner_ty) else_stmts )
  | Scustom_case (ty, scrut, tys, brs, tag) ->
    Scustom_case
      ( ty,
        scrut,
        tys,
        List.map
          (fun (binds, br_ty, stmts) ->
            (binds, br_ty, List.map (replace_return_this_stmt inner_ty) stmts) )
          brs,
        tag )
  | Sswitch (scrut, ind, brs, default) ->
    Sswitch
      ( scrut,
        ind,
        List.map
          (fun (ctor, stmts) ->
            (ctor, List.map (replace_return_this_stmt inner_ty) stmts) )
          brs,
        Option.map (List.map (replace_return_this_stmt inner_ty)) default )
  | Smatch (branches, default) ->
    Smatch
      ( List.map
          (fun br ->
            { br with
              smb_body =
                List.map (replace_return_this_stmt inner_ty) br.smb_body
            })
          branches,
        Option.map (List.map (replace_return_this_stmt inner_ty)) default )
  | Sexpr e -> Sexpr (replace_return_this_expr inner_ty e)
  | s -> s

(** Replace [CPPthis] with [CPPderef CPPthis] in return positions for value-type
    methods.  When a method returns a value type (not shared_ptr), [return this;]
    is invalid because [this] is a pointer.  We need [return *this;] instead. *)
let rec deref_return_this_expr = function
  | CPPthis -> CPPderef CPPthis
  | CPPlambda (params, ret, body, cap) ->
    CPPlambda (params, ret, List.map deref_return_this_stmt body, cap)
  | CPPfun_call (f, args) ->
    CPPfun_call (deref_return_this_expr f,
                 List.map deref_return_this_expr args)
  | CPPoverloaded exprs ->
    CPPoverloaded (List.map deref_return_this_expr exprs)
  | e -> e

and deref_return_this_stmt s =
  ( match s with
  | _ -> () );
  match s with
  | Sreturn (Some e) -> Sreturn (Some (deref_return_this_expr e))
  | Sif (cond, then_stmts, else_stmts) ->
    Sif (cond,
         List.map deref_return_this_stmt then_stmts,
         List.map deref_return_this_stmt else_stmts)
  | Scustom_case (ty, scrut, tys, brs, tag) ->
    Scustom_case (ty, scrut, tys,
      List.map (fun (binds, br_ty, stmts) ->
        (binds, br_ty, List.map deref_return_this_stmt stmts)) brs,
      tag)
  | Sswitch (scrut, ind, brs, default) ->
    Sswitch (scrut, ind,
      List.map (fun (ctor, stmts) ->
        (ctor, List.map deref_return_this_stmt stmts)) brs,
      Option.map (List.map deref_return_this_stmt) default)
  | Smatch (branches, default) ->
    Smatch (List.map (fun br ->
        { br with smb_body = List.map deref_return_this_stmt br.smb_body })
      branches,
      Option.map (List.map deref_return_this_stmt) default)
  | Sexpr e -> Sexpr (deref_return_this_expr e)
  | s -> s

(** Prevent dangling [this] in by-value lambda captures.

    When a methodified function contains a by-value lambda that references
    [this], the lambda may escape the method scope (returned through
    [option], [pair], record, etc.).  The raw [this] pointer dangles once
    the caller's [shared_ptr] is released.

    Fix: bind [shared_from_this()] to a local [_self] at the top of the
    method body, then replace [CPPthis] inside every by-value lambda body
    with [CPPvar "_self"].  The lambda's [=] capture picks up [_self] as
    a [shared_ptr] copy that keeps the object alive.  The outer method
    body keeps raw [CPPthis] for direct method calls (safe because the
    method is invoked on a live object). *)
let replace_this_in_lambdas self_type stmts =
  let id_type ty = ty in
  let self_id = Id.of_string "_self" in
  (* Check if CPPthis or CPPshared_from_this appears in an expression. *)
  let rec expr_has_this = function
    | CPPthis | CPPshared_from_this _ -> true
    | e ->
      let found = ref false in
      ignore (map_expr (fun e' ->
        if expr_has_this e' then found := true; e') (fun s -> s) id_type e);
      !found
  in
  (* Check if CPPthis or CPPshared_from_this appears in statements. *)
  let rec stmt_has_this = function
    | s ->
      let found = ref false in
      ignore (map_stmt
        (fun e -> if expr_has_this e then found := true; e)
        (fun s' -> if stmt_has_this s' then found := true; s')
        id_type s);
      !found
  in
  let stmts_have_this stmts = List.exists stmt_has_this stmts in
  (* Check if any by-value lambda in the method body captures this. *)
  let rec lambda_captures_this_expr = function
    | CPPlambda (_, _, body, true) -> stmts_have_this body
    | e ->
      let found = ref false in
      ignore (map_expr (fun e' ->
        if lambda_captures_this_expr e' then found := true; e')
        (fun s ->
          if lambda_captures_this_stmt s then found := true; s)
        id_type e);
      !found
  and lambda_captures_this_stmt s =
    let found = ref false in
    ignore (map_stmt
      (fun e -> if lambda_captures_this_expr e then found := true; e)
      (fun s' -> if lambda_captures_this_stmt s' then found := true; s')
      id_type s);
    !found
  in
  let needs_self = List.exists lambda_captures_this_stmt stmts in
  if not needs_self then stmts
  else
    (* Determine whether _self is a value type (non-enum).
       Coinductives and regular inductives are both value types. *)
    let is_value_self =
      match self_type with
      | Tglob (self_ref, _, _) -> not (is_enum_inductive self_ref)
      | _ -> false
    in
    (* Substitute CPPthis and CPPshared_from_this → CPPvar "_self" inside
       by-value lambda bodies.  For value-type _self, also collapse
       CPPderef(CPPthis) → CPPvar "_self" to avoid dereferencing a value. *)
    let rec subst_expr = function
      | CPPderef (CPPthis | CPPshared_from_this _) when is_value_self ->
        CPPvar self_id
      | CPPthis | CPPshared_from_this _ -> CPPvar self_id
      | e -> map_expr subst_expr subst_stmt id_type e
    and subst_stmt s =
      map_stmt subst_expr subst_stmt id_type s
    in
    let rec walk_expr = function
      | CPPlambda (params, ret, body, true) ->
        CPPlambda (params, ret, List.map subst_stmt body, true)
      | e -> map_expr walk_expr walk_stmt id_type e
    and walk_stmt s =
      map_stmt walk_expr walk_stmt id_type s
    in
    let self_expr, self_ty =
      if is_value_self then
        (CPPderef CPPthis, Some self_type)
      else
        (CPPshared_from_this self_type, Some (Tshared_ptr self_type))
    in
    let self_binding = Sasgn (self_id, self_ty, self_expr) in
    self_binding :: List.map walk_stmt stmts

(** Check if a C++ type contains [Tshared_ptr] anywhere in its structure.

    Recurses through [Tref], [Tmod], [Tunique_ptr], [Tptr], [Tid], [Tglob],
    [Tnamespace], and [Tfun] to find any nested [Tshared_ptr].

    Used in method generation to gate [replace_return_this_stmt]: the
    [return this] to [return shared_from_this()] transformation is only
    correct when the return type actually wraps the receiver in
    [shared_ptr] (e.g., [shared_ptr<T>] or [pair<shared_ptr<T>, V>]). *)
let rec contains_shared_ptr = function
  | Tshared_ptr _ -> true
  | Tref t | Tmod (_, t) | Tunique_ptr t | Tptr t -> contains_shared_ptr t
  | Tid (_, args) | Tid_external (_, args) | Tglob (_, args, _) ->
    List.exists contains_shared_ptr args
  | Tfun (args, ret) ->
    List.exists contains_shared_ptr args || contains_shared_ptr ret
  | _ -> false

(** Check if any expression or statement contains [CPPshared_from_this]. *)
let rec expr_has_shared_from_this = function
  | CPPshared_from_this _ -> true
  | CPPlambda (_, _, body, _) -> List.exists stmt_has_shared_from_this body
  | CPPfun_call (f, args) ->
    expr_has_shared_from_this f || List.exists expr_has_shared_from_this args
  | CPPoverloaded exprs -> List.exists expr_has_shared_from_this exprs
  | _ -> false

(** Statement-level counterpart of {!expr_has_shared_from_this}: checks whether
    any statement in a method body contains [CPPshared_from_this]. *)
and stmt_has_shared_from_this = function
  | Sreturn (Some e) -> expr_has_shared_from_this e
  | Sexpr e -> expr_has_shared_from_this e
  | Sif (_, then_stmts, else_stmts) ->
    List.exists stmt_has_shared_from_this then_stmts
    || List.exists stmt_has_shared_from_this else_stmts
  | Scustom_case (_, _, _, brs, _) ->
    List.exists
      (fun (_, _, stmts) -> List.exists stmt_has_shared_from_this stmts)
      brs
  | Sswitch (_, _, brs, default) ->
    List.exists
      (fun (_, stmts) -> List.exists stmt_has_shared_from_this stmts)
      brs
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Smatch (branches, default) ->
    List.exists
      (fun br -> List.exists stmt_has_shared_from_this br.smb_body)
      branches
    || (match default with Some stmts -> List.exists stmt_has_shared_from_this stmts | None -> false)
  | Sasgn (_, _, e) -> expr_has_shared_from_this e
  | _ -> false

(** Generate a single method from a method candidate. name: the containing
    type's GlobRef vars: type variables of the containing type (func_ref, body,
    ty, this_pos): the method candidate *)
let gen_single_method name vars (func_ref, body, ty, this_pos) =
  let num_ind_vars = List.length vars in
  let func_name = Id.of_string (Common.pp_global_name Term func_ref) in

  (* Get return type *)
  let all_args, ret_ty = get_args_and_ret [] ty in

  (* Determine the mapping from function type variables to inductive type
     variables. For same-module methods, the function uses Tvars 1..num_ind_vars
     for the inductive. For cross-module methods, the function may use different
     Tvar positions. We extract the actual mapping from the Tglob at this_pos.

     Example: fold_left has type (A → B → A) → list B → A → A where A=Tvar1
     (accumulator), B=Tvar2 (list element). list<B> uses Tvar2, so ind_tvar_map
     = [(2, 1)] meaning "Tvar2 → ind var position 1". Then Tvar1 is "extra" and
     becomes template param T1. *)
  let ind_tvar_map =
    match List.nth_opt all_args this_pos with
    | Some (Miniml.Tglob (_, tvar_args, _)) ->
      (* Extract Tvar indices from the Tglob args, paired with their position *)
      List.concat
        (List.mapi
           (fun pos t ->
             match t with
             | Miniml.Tvar i | Miniml.Tvar' i -> [(i, pos + 1)]
             | _ -> [] )
           tvar_args )
    | _ ->
      (* Fallback for non-template types: assume positions 1..num_ind_vars *)
      List.init num_ind_vars (fun i -> (i + 1, i + 1))
  in
  let ind_tvar_set = IntSet.of_list (List.map fst ind_tvar_map) in
  (* Remap ML type variables: assign canonical positions so
     convert_ml_type_to_cpp_type maps them correctly. - Inductive tvars →
     positions 1..num_ind_vars - Extra tvars → positions num_ind_vars+1,
     num_ind_vars+2, ... This avoids collisions when the function uses different
     numbering than the inductive.

     Example: fold_left has Tvar1 (accum), Tvar2 (list elem) ind_tvar_map = [(2,
     1)] — Tvar2 is the list element → position 1 extra tvars: [1] — Tvar1 is
     extra → position 2 (= num_ind_vars + 1) Full remap: Tvar1 → 2, Tvar2 → 1 *)
  let all_tvars = List.sort compare (collect_tvars [] ty) in
  let extra_tvars_orig =
    List.filter (fun i -> not (IntSet.mem i ind_tvar_set)) all_tvars
  in
  let needs_remap =
    (not (List.for_all (fun (src, dst) -> src = dst) ind_tvar_map))
    || extra_tvars_orig <> []
  in
  (* Build complete remap table: (original_idx → canonical_idx) *)
  let extra_remap =
    List.mapi (fun i orig -> (orig, num_ind_vars + 1 + i)) extra_tvars_orig
  in
  let full_remap = ind_tvar_map @ extra_remap in
  let remap_ml_tvar i =
    match List.assoc_opt i full_remap with
    | Some canonical -> canonical
    | None -> i
  in
  let rec remap_ml_type = function
    | Miniml.Tvar i -> Miniml.Tvar (remap_ml_tvar i)
    | Miniml.Tvar' i -> Miniml.Tvar' (remap_ml_tvar i)
    | Miniml.Tarr (t1, t2) -> Miniml.Tarr (remap_ml_type t1, remap_ml_type t2)
    | Miniml.Tglob (r, args, e) ->
      Miniml.Tglob (r, List.map remap_ml_type args, e)
    | Miniml.Tmeta {contents = Some t} -> remap_ml_type t
    | t -> t
  in
  let _ty = if needs_remap then remap_ml_type ty else ty in
  let ret_ty = if needs_remap then remap_ml_type ret_ty else ret_ty in
  let body =
    if needs_remap then Mlutil.remap_tvars remap_ml_tvar body else body
  in
  (* After remapping, extra tvars are at positions num_ind_vars+1,
     num_ind_vars+2, ... *)
  let extra_tvars = List.map snd extra_remap in
  let extra_tvar_names = List.mapi (fun i _ -> tvar_id (i + 1)) extra_tvars in
  let extra_tvar_map = List.combine extra_tvars extra_tvar_names in
  let subst_extra_tvars = make_subst_extra_tvars num_ind_vars extra_tvar_map in

  (* For type conversion in method contexts, use ns = {name} so that
     self-references INSIDE container types get shared_ptr wrapping
     (matching how struct fields are defined).  Then strip the top-level
     shared_ptr for the method's own type (value-type inductives are
     passed/returned by value, not by shared_ptr). *)
  let method_ns = Refset'.add name Refset'.empty in
  let rec strip_self_ptr ty =
    match ty with
    | Tshared_ptr (Tglob (g, _, _)) when not (is_enum_inductive g) ->
      (match ty with Tshared_ptr inner -> inner | _ -> ty)
    | Tunique_ptr (Tglob (g, _, _)) when not (is_enum_inductive g) ->
      (match ty with Tunique_ptr inner -> inner | _ -> ty)
    | Tglob (r, args, es) ->
      Tglob (r, List.map strip_self_ptr args, es)
    | Tfun (args, ret) ->
      Tfun (List.map strip_self_ptr args, strip_self_ptr ret)
    | Tref t -> Tref (strip_self_ptr t)
    | Tmod (m, t) -> Tmod (m, strip_self_ptr t)
    | _ -> ty
  in
  let strip_top_level_self_ptr ty = strip_self_ptr ty in
  let ret_cpp =
    convert_ml_type_to_cpp_type
      (empty_env ())
      method_ns
      vars
      ret_ty
  in
  let ret_cpp = strip_top_level_self_ptr ret_cpp in
  let ret_cpp = subst_extra_tvars ret_cpp in

  (* Collect lambda parameters and build environment for de Bruijn lookup.
     push_vars' may rename duplicate parameters (e.g., two params named 't'
     become 't', 't0').

     We must use the renamed ids (all_ids) consistently for: 1. The environment
     - so gen_expr/gen_stmts produce correct variable references 2. The C++
     method signature - so parameter names match what the body references

     Previously, renamed ids were discarded and original names used for the
     signature, causing errors like: void method(tree t) { ... t0->v() ... }
     where 't0' in the body didn't exist as a parameter. *)
  let ids_with_types, inner_body = Mlutil.collect_lams body in
  let ids_converted =
    List.map
      (fun (x, ty) -> (remove_prime_id (id_of_mlid x), ty))
      ids_with_types
  in
  let all_ids, env = push_vars' ids_converted (empty_env ()) in
  reset_env_types ();
  push_env_types all_ids;
  (* Infer owned/borrowed for method parameters. Note: method 'this' is always
     borrowed (const method). *)
  let n_method_params = List.length ids_with_types in
  let method_owned_flags =
    Escape.infer_owned_params n_method_params inner_body
  in

  (* Extract 'this' argument at this_pos - use renamed ids for consistency with
     body *)
  let ids_normal_order = List.rev all_ids in
  let this_arg_id_opt, param_ids_with_pos =
    Common.extract_at_pos
      this_pos
      (List.mapi (fun i (id, ty) -> (id, ty, i)) ids_normal_order)
  in
  let this_arg_id = Option.map (fun (id, _, _) -> id) this_arg_id_opt in
  let param_ids_with_pos =
    List.filter (fun (_, ty, _) -> not (ml_type_is_void ty)) param_ids_with_pos
  in

  (* Build owned flag lookup for non-this params. ids_normal_order is
     outermost-first. de Bruijn index of element i in normal order =
     n_method_params - i. method_owned_flags[db - 1] gives the owned flag. *)
  let get_param_owned_flag normal_order_idx =
    let db = n_method_params - normal_order_idx in
    match List.nth_opt method_owned_flags (db - 1) with
    | Some b -> b
    | None -> false
  in

  (* Convert params to C++ types.  Use method_ns so that self-references
     inside container types get shared_ptr (matching struct field types).
     Strip top-level shared_ptr since value-type params are bare values. *)
  let params_with_idx =
    List.mapi
      (fun i (id, ty, orig_idx) ->
        let cpp_ty =
          convert_ml_type_to_cpp_type
            env
            method_ns
            vars
            ty
        in
        let cpp_ty = strip_top_level_self_ptr cpp_ty in
        let cpp_ty = subst_extra_tvars cpp_ty in
        let owned = get_param_owned_flag orig_idx in
        (id, cpp_ty, i, owned) )
      param_ids_with_pos
  in

  (* Extract function-typed parameters for template params *)
  let fun_params =
    List.filter_map
      (fun (id, cpp_ty, i, _) ->
        match cpp_ty with
        | Tfun (dom, cod) ->
          let cod = if is_cpp_unit_type cod then Tvoid else cod in
          Some (id, TTfun (dom, cod), fun_tparam_id i)
        | _ -> None )
      params_with_idx
  in

  (* Build template params *)
  let extra_type_params =
    List.map (fun name -> (TTtypename, name)) extra_tvar_names
  in
  let fun_template_params =
    List.map (fun (_, tt, fname) -> (tt, fname)) fun_params
  in
  let template_params = extra_type_params @ fun_template_params in

  (* Build final params with proper wrapping. Use escape analysis to determine
     owned vs borrowed: owned params are passed by value (for move semantics),
     borrowed params are passed by const ref. This matches gen_dfun's logic to
     ensure forward declarations and definitions agree. *)
  let params =
    List.map
      (fun (id, cpp_ty, i, owned) ->
        let wrapped =
          match cpp_ty with
          | Tfun _ -> Tref (Tref (Tvar (0, Some (fun_tparam_id i))))
          | _ -> wrap_param_by_ownership ~is_owned:owned cpp_ty
        in
        (id, wrapped) )
      params_with_idx
  in

  (* For coinductive return types, wrap return in lazy thunk *)
  let is_cofix_method = Table.is_coinductive_type ret_ty in
  let method_k x =
    if is_cofix_method then
      let type_args =
        match ret_ty with
        | Miniml.Tglob (_, args, _) ->
          List.map
            (fun t ->
              convert_ml_type_to_cpp_type
                (empty_env ())
                (Refset'.add name Refset'.empty)
                vars
                t )
            args
        | _ -> []
      in
      let coind_ref =
        match ret_ty with
        | Miniml.Tglob (r, _, _) -> r
        | _ ->
          CErrors.anomaly
            (Pp.str
               "gen_method_field: cofixpoint return type expected to be Tglob" )
      in
      let lazy_factory =
        CPPqualified
          (mk_cppglob coind_ref type_args, Id.of_string "lazy_")
      in
      let thunk = CPPlambda ([], Some ret_cpp, [Sreturn (Some x)], true) in
      Sreturn (Some (CPPfun_call (lazy_factory, [thunk])))
    else
      Sreturn (Some x)
  in
  (* Generate method body. Initialize move tracking for owned parameters.
     'this' is always borrowed (const method). *)
  let saved_dead = tctx.move_dead_after in
  let saved_owned = tctx.move_owned_vars in
  let saved_nparams = tctx.move_n_params in
  let saved_type_vars = get_current_type_vars () in
  tctx.move_dead_after <- Escape.IntSet.empty;
  (* Initialize owned-variable tracking for method parameters.
     The de Bruijn environment has parameters in reverse order:
     ids_normal_order has outermost-first, push_vars' reverses them. *)
  let method_n_params = List.length ids_with_types in
  tctx.move_n_params <- method_n_params;
  (* method_owned_flags[i] corresponds to de Bruijn index i+1.
     db index i+1 maps to ids_with_types[i] (outermost-first, same order
     as push_vars' which prepends in list order).
     Only track ownership for non-trivial types (inductives). *)
  tctx.move_owned_vars <-
    List.fold_left
      (fun acc (i, owned) ->
        if owned then
          let ml_ty = snd (List.nth ids_with_types i) in
          if Escape.is_shared_ptr_type ml_ty then
            Escape.IntSet.add (i + 1) acc
          else acc
        else acc )
      Escape.IntSet.empty
      (List.mapi (fun i o -> (i, o)) method_owned_flags);
  tctx.match_param_counter <- 0;
  tctx.cs_counter <- 0;
  tctx.current_letin_depth <- 0;
  (* Set current type vars to include both the inductive's type vars and extra
     tvars. This ensures gen_expr/eta_fun correctly convert Tvars to named C++
     types when processing the method body (e.g., recursive calls carry type
     args). *)
  set_current_type_vars (vars @ extra_tvar_names);
  let saved_method_ns = tctx.method_self_ns in
  (* Include all local value-type inductives with recursive fields in the
     method ns.  This ensures that when the method body constructs or
     manipulates containers of recursive types (e.g. List<tree>), the
     type arguments get shared_ptr wrapping to match struct field types. *)
  let full_method_ns =
    List.fold_left
      (fun acc g ->
        if Table.has_recursive_fields g && not (is_enum_inductive g)
        then Refset'.add g acc
        else acc)
      method_ns
      (get_local_inductives ())
  in
  tctx.method_self_ns <- full_method_ns;
  let stmts = gen_stmts env method_k inner_body in
  tctx.method_self_ns <- saved_method_ns;
  set_current_type_vars saved_type_vars;
  tctx.move_dead_after <- saved_dead;
  tctx.move_owned_vars <- saved_owned;
  tctx.move_n_params <- saved_nparams;
  (* Add type args to recursive self-calls. Inside fixpoint bodies, the
     extraction produces MLglob(func_ref, []) with empty type args for recursive
     references. When the function is a method, the recursive call needs
     explicit template args for non-deducible params. Replace CPPglob(func_ref,
     []) with CPPglob(func_ref, all_type_args).

     The type args must be in the ORIGINAL tys order (matching
     ind_tvar_positions used by pp_cpp_expr for filtering). Position i in tys
     corresponds to Tvar (i+1) in the original ML type. After remapping, Tvar
     (i+1) → remap_ml_tvar(i+1). We construct the C++ type arg from
     extended_vars at that remapped position. *)
  let extended_vars = vars @ extra_tvar_names in
  let all_method_type_args =
    List.map
      (fun orig_tvar_idx ->
        let remapped = remap_ml_tvar orig_tvar_idx in
        let name = List.nth extended_vars (remapped - 1) in
        Tvar (remapped - 1, Some name) )
      all_tvars
  in
  let stmts =
    if all_method_type_args <> [] then
      let self_call_with_tys = mk_cppglob func_ref all_method_type_args in
      List.map (glob_subst_stmt func_ref self_call_with_tys) stmts
    else
      stmts
  in
  let stmts =
    match this_arg_id with
    | Some id ->
      (* For value-type methods, substitute with [CPPderef CPPthis] so that
         return positions produce a value copy rather than a raw pointer.
         For shared_ptr/coinductive methods, keep bare [CPPthis]. *)
      let this_expr =
        if not (Table.is_coinductive name) && not (is_enum_inductive name) then
          CPPderef CPPthis
        else CPPthis
      in
      List.map (var_subst_stmt id this_expr) stmts
    | None -> stmts
  in
  (* Replace [CPPthis] with [CPPshared_from_this] in return expressions.  When a
     method body returns or stores [this] in a position that expects [shared_ptr]
     (e.g. [return this;], [return std::make_pair(this, this);]), the raw pointer
     cannot convert to [shared_ptr].  Using [shared_from_this()] produces a valid
     [shared_ptr] from the raw pointer.  Only applied when the return type
     contains [shared_ptr] (e.g. [shared_ptr<T>], [pair<shared_ptr, shared_ptr>])
     to avoid replacing [this] in method calls that just forward the receiver. *)
  (* Compute self_type unconditionally — needed by both return-this and
     lambda-this passes. *)
  let self_type_args =
    List.mapi (fun i vname -> Tvar (i, Some vname)) vars
  in
  let self_type = Tglob (name, self_type_args, []) in
  let stmts =
    if contains_shared_ptr ret_cpp then
      List.map (replace_return_this_stmt self_type) stmts
    else stmts
  in
  (* Replace [CPPthis] with [CPPshared_from_this] inside by-value lambda
     bodies.  When a method returns a closure that captures [this], the raw
     pointer would dangle after the caller's [shared_ptr] is released.
     Using [shared_from_this()] inside the lambda ensures the closure keeps
     the object alive. *)
  let stmts = return_captures_by_value stmts in
  let stmts = replace_this_in_lambdas self_type stmts in
  (* Apply tvar_subst_stmt with the extended vars list (defined above).
     extended_vars covers positions 1..num_ind_vars (inductive vars) and
     num_ind_vars+1, num_ind_vars+2, etc. (extra vars) so tvar_subst_stmt can
     name them all correctly. *)
  let stmts = List.map (tvar_subst_stmt extended_vars) stmts in

  let no_pure = is_monadic_ml_type ret_ty in
  ( Fmethod
      {
        mf_name = func_name;
        mf_tparams = template_params;
        mf_ret_type = ret_cpp;
        mf_params = params;
        mf_body = stmts;
        mf_is_const = true;
        mf_is_static = false;
        mf_is_inline = false;
        mf_this_pos = this_pos;
        mf_no_pure = no_pure;
      },
    VPublic,
    SNoTag )

(** Generate C++ header for an inductive type (v2 style: encapsulated struct
    with methods).

    Produces a self-contained struct with:
    - Nested constructor-alternative structs (e.g. [Leaf {}], [Node { ... }])
    - [using variant_t = std::variant<Leaf, Node>]
    - Private [variant_t d_v_] data member
    - Explicit constructors for each alternative
    - Static factory methods ([cons(...)], [cons_uptr(...)]) with move semantics
    - Methods from [method_candidates] (with [this] substitution)

    @param consarg_names  binder names from {!Miniml.ml_ind_packet.ip_consarg_names};
      when provided, constructor struct fields and factory parameters use
      descriptive names derived from the Rocq source instead of [d_a0] etc. *)

(** Does the ML type [ml_ty] contain [ind_ref] (or a mutual sibling) anywhere
    in its type arguments — but NOT at the top level?  Used to detect fields
    like [list(tree(A))] inside [tree]'s definition, which need field-level
    [unique_ptr] wrapping instead of type-argument wrapping. *)
let ml_type_has_nested_self_ref ~ind_ref ml_ty =
  let ind_kn_opt =
    match ind_ref with
    | GlobRef.IndRef (kn, _) -> Some kn
    | _ -> None
  in
  let is_self_or_mutual r =
    Environ.QGlobRef.equal Environ.empty_env r ind_ref
    || match r, ind_kn_opt with
       | GlobRef.IndRef (kn2, _), Some kn ->
         MutInd.CanOrd.equal kn2 kn
       | _ -> false
  in
  let rec has_self_ref = function
    | Miniml.Tglob (r, args, _) ->
      is_self_or_mutual r || List.exists has_self_ref args
    | Miniml.Tmeta {contents = Some t} -> has_self_ref t
    | Miniml.Tarr (t1, t2) ->
      has_self_ref t1 || has_self_ref t2
    | _ -> false
  in
  match ml_ty with
  | Miniml.Tglob (r, args, _) when not (is_self_or_mutual r) ->
    List.exists has_self_ref args
  | Miniml.Tmeta {contents = Some (Miniml.Tglob (r, args, _))}
    when not (is_self_or_mutual r) ->
    List.exists has_self_ref args
  | _ -> false

(** Check whether the self/mutual reference inside [ml_ty] is uniform
    (i.e. its type arguments are exactly the parent's type parameters
    in order).  Non-uniform recursion needs [shared_ptr]. *)
let ml_self_ref_is_uniform ~ind_ref ~cname ml_ty =
  let ind_kn_opt =
    match ind_ref with
    | GlobRef.IndRef (kn, _) -> Some kn
    | _ -> None
  in
  let is_self_or_mutual r =
    Environ.QGlobRef.equal Environ.empty_env r ind_ref
    || match r, ind_kn_opt with
       | GlobRef.IndRef (kn2, _), Some kn ->
         MutInd.CanOrd.equal kn2 kn
       | _ -> false
  in
  let rec find_self_ref_args = function
    | Miniml.Tglob (r, args, _) when is_self_or_mutual r -> Some args
    | Miniml.Tglob (_, args, _) ->
      List.find_map find_self_ref_args args
    | Miniml.Tmeta {contents = Some t} -> find_self_ref_args t
    | _ -> None
  in
  match find_self_ref_args ml_ty with
  | Some args ->
    let n_params = Table.get_ctor_num_param_vars cname in
    List.length args = n_params
    && List.for_all (fun (j, arg) ->
      match arg with
      | Miniml.Tvar k | Miniml.Tvar' k -> k = j + 1
      | Miniml.Tmeta {contents = Some (Miniml.Tvar k)}
      | Miniml.Tmeta {contents = Some (Miniml.Tvar' k)} -> k = j + 1
      | _ -> false
    ) (List.mapi (fun j a -> (j, a)) args)
  | None -> true

let gen_ind_header_v2
    ?(is_mutual = false)
    ?(consarg_names = [||])
    vars
    name
    cnames
    tys
    method_candidates
    ind_kind =
  let is_coinductive = ind_kind = Coinductive in
  let templates = List.map (fun n -> (TTtypename, n)) vars in
  let ty_vars = List.mapi (fun i x -> Tvar (i, Some x)) vars in

  (* Handle empty inductives (no constructors) - generate uninhabitable
     struct *)
  if Array.length cnames = 0 then
    (* For empty types like `Inductive empty : Type := .`, generate: struct
       empty { empty() = delete; }; This type cannot be constructed, matching
       the semantics of empty types. *)
    let method_fields =
      List.map (gen_single_method name vars) method_candidates
    in
    Dstruct
      {
        ds_ref = name;
        ds_fields = [(Fdeleted_ctor, VPublic, SNoTag)] @ method_fields;
        ds_tparams = templates;
        ds_constraint = None;
        ds_needs_shared_from_this = false;
      }
  else (* Check if all constructors are nullary: eligible for enum class *)
    let all_nullary = Array.for_all (fun tys_list -> tys_list = []) tys in
    if all_nullary && vars = [] && (not is_mutual) && not (is_custom name) then (
      (* Register as enum inductive for type/constructor/match generation *)
      Table.add_enum_inductive name;
      let ctor_names =
        Array.to_list
          (Array.map
             (fun c ->
               match c with
               | GlobRef.ConstructRef _ ->
                 Id.of_string
                   (Common.enum_ctor_name (Common.pp_global_name Type c))
               | _ -> ctor_fallback_id 0 )
             cnames )
      in
      let rocq_names =
        Array.to_list
          (Array.map
             (fun c ->
               match c with
               | GlobRef.ConstructRef _ -> Common.pp_global_name Type c
               | _ -> "" )
             cnames )
      in
      Denum
        {
          de_ref = name;
          de_ctors = ctor_names;
          de_ctor_rocq_names = rocq_names;
          de_tparams = [];
        } )
    else
      (* The main struct type: all inductives (including coinductives)
         are value types. *)
      let self_ty = Tglob (name, ty_vars, []) in

      (* 1. Constructor alternative structs (simple, just fields, no make) *)
      let constructor_structs =
        Array.to_list
          (Array.mapi
             (fun i tys_list ->
               let c = cnames.(i) in
               let cname = ctor_struct_id_of_ref ~fallback_idx:i c in
               (* Fields: convert types, using self_ty for recursive
                  references *)
               let ctor_struct_name = Id.to_string cname in
               let ctor_consarg_names =
                 if i < Array.length consarg_names then consarg_names.(i)
                 else []
               in
               let n_fields = List.length tys_list in
               let field_ids =
                 compute_and_register_field_names
                   ctor_struct_name ctor_consarg_names n_fields
               in
               let fields =
                 List.mapi
                   (fun j ty ->
                     let cpp_ty =
                       convert_ml_type_to_cpp_type
                         (empty_env ())
                         (Refset'.add name Refset'.empty)
                         vars
                         ty
                     in
                     (* Wrap fields that contain a nested self-reference in
                        their type arguments (e.g. list(tree(A)) inside tree).
                        The cycle is broken at the field level, not the type-arg
                        level, so type variables are always bare types. *)
                     let cpp_ty =
                       if ml_type_has_nested_self_ref ~ind_ref:name ty
                       then
                         if is_coinductive then Tshared_ptr cpp_ty
                         else if ml_self_ref_is_uniform ~ind_ref:name ~cname:c ty
                         then Tunique_ptr cpp_ty
                         else Tshared_ptr cpp_ty
                       else cpp_ty
                     in
                     (* For indexed inductives (no template params), erase
                        unnamed Tvars to std::any *)
                     let cpp_ty =
                       if vars = [] then tvar_erase_type cpp_ty else cpp_ty
                     in
                     let field_name = List.nth field_ids j in
                     (Fvar (field_name, cpp_ty), VPublic, SNoTag) )
                   tys_list
               in
               (Fnested_struct (cname, fields), VPublic, STypes) )
             tys )
      in

      (* 2. variant_t type alias - use simple Id-based refs that match nested struct names *)
      (* Note: nested structs inherit template params from parent, so don't add <A> to them *)
      let variant_ty =
        Tvariant
          (Array.to_list
             (Array.mapi
                (fun i c ->
                  let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                  (* Use Tid for local nested struct types - no template args
                     since they inherit *)
                  Tid (cname_id, []) )
                cnames ) )
      in
      let variant_using =
        (Fnested_using (Id.of_string "variant_t", variant_ty), VPublic, STypes)
      in
      let element_using = [] in

      (* 3. Private variant member: v_ for inductive, lazy_v_ for coinductive *)
      let variant_member_name = if is_coinductive then "d_lazyV_" else "d_v_" in
      let variant_member_ty =
        if is_coinductive then
          Tid
            ( Id.of_string_soft "crane::lazy",
              [Tid (Id.of_string "variant_t", [])] )
        else
          Tid (Id.of_string "variant_t", [])
      in
      let variant_member =
        ( Fvar (Id.of_string variant_member_name, variant_member_ty),
          VPrivate,
          SData )
      in

      (* 4. Public explicit constructors for each alternative.
         Public so that std::make_shared / std::make_unique can construct
         instances directly (single allocation). *)
      (* Note: nested struct types don't need template args - they inherit from parent *)
      let public_ctors =
        Array.to_list
          (Array.mapi
             (fun i c ->
               let cname = ctor_struct_id_of_ref ~fallback_idx:i c in
               let param_name = Id.of_string "_v" in
               let param_ty = Tid (cname, []) in
               if is_coinductive then
                 (* For coinductive:
                    d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) *)
                 let init_expr =
                   CPPfun_call
                     ( CPPvar (Id.of_string_soft "crane::lazy<variant_t>"),
                       [
                         CPPfun_call
                           ( CPPvar (Id.of_string "variant_t"),
                             [CPPmove (CPPvar param_name)] );
                       ] )
                 in
                 let init_list = [(Id.of_string "d_lazyV_", init_expr)] in
                 ( Fconstructor ([(param_name, param_ty)], init_list, true),
                   VPublic,
                   SCreators )
               else
                 (* For inductive: d_v_(std::move(_v)) when the constructor
                    struct has non-trivial fields (shared_ptr etc.).  For
                    trivially-copyable structs (e.g., empty nullary constructors
                    like O, Nil, Leaf), skip std::move — it has no effect and
                    triggers performance-move-const-arg. *)
                 let has_nontrivial_fields =
                   List.exists (fun ty -> not (isTdummy ty)) tys.(i)
                 in
                 let init_v =
                   if has_nontrivial_fields then CPPmove (CPPvar param_name)
                   else CPPvar param_name
                 in
                 let init_list =
                   [(Id.of_string "d_v_", init_v)]
                 in
                 ( Fconstructor ([(param_name, param_ty)], init_list, true),
                   VPublic,
                   SCreators ) )
             cnames )
      in

      (* Default constructor for value-type inductives.  The variant
         default-constructs to its first alternative (e.g. Nil), which lets
         loopify declare [T _result{};] for stack-based iteration. *)
      let default_ctor =
        if not is_coinductive then
          [( Fconstructor ([], [], false),
             VPublic,
             SCreators )]
        else
          []
      in

      (* Value-type inductives store direct recursive fields as
         [std::unique_ptr].  The default destructor recursively destroys a deep
         list/tree through the C++ call stack, which overflows on the deep
         regression tests.  For direct self-recursive fields, drain those
         pointers iteratively before the variant is destroyed. *)
      let iterative_destructor =
        if is_coinductive then []
        else
          let rec is_direct_self_ref = function
            | Miniml.Tglob (r, args, _) ->
              Environ.QGlobRef.equal Environ.empty_env r name
              && List.length args = List.length vars
              && List.for_all
                   (fun (j, arg) ->
                     match arg with
                     | Miniml.Tvar k | Miniml.Tvar' k -> k = j + 1
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar k)}
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar' k)} ->
                       k = j + 1
                     | _ -> false)
                   (List.mapi (fun j a -> (j, a)) args)
            | Miniml.Tmeta {contents = Some t} -> is_direct_self_ref t
            | _ -> false
          in
          let ctor_moves =
            Array.to_list
              (Array.mapi
                 (fun i tys_list ->
                   let recursive_fields =
                     List.filter_map
                       (fun (j, ty) ->
                         if is_direct_self_ref ty then
                           let cname =
                             ctor_struct_name_of_ref ~fallback_idx:i cnames.(i)
                           in
                           Some (Id.to_string (lookup_ctor_field_name cname j))
                         else None)
                       (List.mapi (fun j ty -> (j, ty)) tys_list)
                   in
                   match recursive_fields with
                   | [] -> None
                   | fields ->
                     let ctor_id =
                       Id.to_string (ctor_struct_id_of_ref ~fallback_idx:i cnames.(i))
                     in
                     let moves =
                       List.map
                         (fun field ->
                           "        if (_alt." ^ field
                           ^ ") _stack.push_back(std::move(_alt." ^ field
                           ^ "));")
                         fields
                     in
                     Some
                       (String.concat "\n"
                          (("      if (std::holds_alternative<" ^ ctor_id
                            ^ ">(_node.d_v_)) {")
                           :: ("        auto &_alt = std::get<" ^ ctor_id
                               ^ ">(_node.d_v_);")
                           :: moves @ ["      }"])))
                 tys)
              |> List.filter_map Fun.id
          in
          match ctor_moves with
          | [] -> []
          | moves ->
            let body =
              String.concat "\n"
                (["~%SELF%() {";
                  "  std::vector<std::unique_ptr<%SELF%>> _stack;";
                  "  auto _drain = [&](%SELF% &_node) {"]
                 @ moves
                 @ ["  };";
                    "  _drain(*this);";
                    "  while (!_stack.empty()) {";
                    "    auto _node = std::move(_stack.back());";
                    "    _stack.pop_back();";
                    "    if (_node) _drain(*_node);";
                    "  }";
                    "}"])
            in
            [(Fraw body, VPublic, SManipulators)]
      in

      (* For coinductive types, add public constructor accepting
         std::function<variant_t()> (public so make_shared can access it) *)
      let lazy_ctor =
        if is_coinductive then
          let param_name = Id.of_string "_thunk" in
          let variant_t_ty = Tid (Id.of_string "variant_t", []) in
          let param_ty = Tfun ([], variant_t_ty) in
          let init_expr =
            CPPfun_call
              ( CPPvar (Id.of_string_soft "crane::lazy<variant_t>"),
                [CPPmove (CPPvar param_name)] )
          in
          let init_list = [(Id.of_string "d_lazyV_", init_expr)] in
          [
            ( Fconstructor ([(param_name, param_ty)], init_list, true),
              VPublic,
              SCreators );
          ]
        else
          []
      in

      (* 5. Static factory methods.  Each constructor gets one factory
         method as a direct static member of the struct, returning by value.

         Factory names are the lowercase of the constructor struct name
         (e.g., Cons → cons).  If this collides with a C++ keyword or the
         type's own name, the factory falls back to PascalCase with trailing
         underscore (e.g., Char → Char_).  See {!factory_name_of_ctor}.

         Move semantics: All parameters use the "sink parameter" idiom
         (passed by value, std::move'd into the struct initializer).
         Recursive (unique_ptr) fields take the inner type by value and
         are wrapped in make_unique internally. *)
      let ind_type_name = Common.pp_global_name Type name in

      let mk_factory_methods ret_ty wrap_expr i tys_list =
        let c = cnames.(i) in
        let cname = ctor_struct_name_of_ref ~fallback_idx:i c in
        let fname =
          factory_name_of_ctor ~type_name:ind_type_name cname
        in
        let factory_name = Id.of_string fname in
        (* Convert ML types both as public API types and constructor storage
           types.  Public APIs remain value-shaped (empty ns); storage uses
           [name] in ns so recursive occurrences are owned unique_ptrs. *)
        let cpp_tys =
          List.mapi
            (fun j ty ->
              let storage_ty =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  (Refset'.add name Refset'.empty)
                  vars
                  ty
              in
              (* Wrap fields with nested self-refs at the field level *)
              let storage_ty =
                if ml_type_has_nested_self_ref ~ind_ref:name ty
                then
                  if is_coinductive then Tshared_ptr storage_ty
                  else if ml_self_ref_is_uniform ~ind_ref:name ~cname:c ty
                  then Tunique_ptr storage_ty
                  else Tshared_ptr storage_ty
                else storage_ty
              in
              let api_ty =
                convert_ml_type_to_cpp_type
                  (empty_env ())
                  Refset'.empty
                  vars
                  ty
              in
              let storage_ty =
                if vars = [] then tvar_erase_type storage_ty else storage_ty
              in
              let api_ty =
                if vars = [] then tvar_erase_type api_ty else api_ty
              in
              (j, storage_ty, api_ty) )
            tys_list
        in
        (* Derive factory parameter name from the registered field name.
           Factory params use the bare binder name (e.g. [left]) rather than
           the prefixed field name (e.g. [d_left]), since they are function
           parameters, not struct members.  Falls back to the full field id
           if stripping the [d_] prefix fails. *)
        let param_name_of j =
          let field_id = lookup_ctor_field_name cname j in
          let s = Id.to_string field_id in
          if String.length s > 2 && s.[0] = 'd' && s.[1] = '_' then
            Id.of_string (String.sub s 2 (String.length s - 2))
          else field_id
        in
        (* For owned recursive fields in value-type inductives, factory
           params take the inner value by value (sink parameter) so callers
           can move in.  Coinductive shared_ptr fields stay as const ref. *)
        let params =
          List.map
            (fun (j, storage_ty, api_ty) ->
              let param_ty =
                match storage_ty with
                | Tunique_ptr inner ->
                  inner
                | Tshared_ptr inner ->
                  Tref (Tmod (TMconst, inner))
                | _ -> api_ty
              in
              (param_name_of j, param_ty) )
            cpp_tys
        in
        let ctor_args =
          List.map
            (fun (j, storage_ty, api_ty) ->
              let var = CPPvar (param_name_of j) in
              match storage_ty with
              | Tfun (storage_args, storage_ret) -> begin
                match api_ty with
                | Tfun (api_args, api_ret) when List.length storage_args = List.length api_args
                  && storage_ty <> api_ty ->
                  let lambda_params =
                    List.mapi
                      (fun k storage_arg ->
                        (storage_arg, Some (Id.of_string ("x" ^ string_of_int k)))
                      )
                      storage_args
                  in
                  let call_args =
                    List.mapi
                      (fun k (_storage_arg, api_arg) ->
                        let arg_var =
                          CPPvar (Id.of_string ("x" ^ string_of_int k))
                        in
                        if _storage_arg = api_arg then
                          arg_var
                        else
                          gen_clone_field_expr
                            ~src_ty:_storage_arg ~dst_ty:api_arg
                            arg_var )
                      (List.combine storage_args api_args)
                  in
                  let call = CPPfun_call (var, List.rev call_args) in
                  let ret =
                    if storage_ret = api_ret then
                      call
                    else
                      gen_clone_field_expr
                        ~src_ty:api_ret ~dst_ty:storage_ret
                        call
                  in
                  CPPlambda
                    ( List.rev lambda_params,
                      None,
                      [Sreturn (Some ret)],
                      true )
                | _ when storage_ty = api_ty -> CPPmove var
                | _ ->
                  gen_clone_field_expr
                    ~src_ty:api_ty ~dst_ty:storage_ty var
              end
              | Tunique_ptr inner ->
                CPPfun_call (CPPmk_unique inner, [CPPmove var])
              | Tshared_ptr inner when is_coinductive ->
                CPPfun_call (CPPmk_shared inner, [var])
              | Tshared_ptr _ ->
                CPPraw
                  ("(static_cast<void>("
                  ^ Id.to_string (param_name_of j)
                  ^ "), nullptr)")
              | _ when storage_ty = api_ty -> CPPmove var
              | _ ->
                gen_clone_field_expr
                  ~src_ty:api_ty ~dst_ty:storage_ty var )
            cpp_tys
        in
        let ctor_struct =
          CPPstruct_id (Id.of_string cname, [], ctor_args)
        in
        let body = [Sreturn (Some (wrap_expr ctor_struct))] in
        let primary =
          ( Ffundef (factory_name, Tmod (TMstatic, ret_ty), params, body),
            VPublic,
            SCreators )
        in
        [primary]
      in
      let factory_methods =
        List.flatten
          (Array.to_list
             (Array.mapi
                (mk_factory_methods self_ty
                   (* Wrap constructor struct in parent type constructor:
                      O{} → Nat(O{}) — needed because constructors are
                      explicit. Use CPPglob with the inductive ref so
                      the printer emits the correct name (handles both
                      top-level and module-nested inductives). *)
                   (fun s -> CPPfun_call (mk_cppglob name [], [s])) )
                tys ) )
      in

      (* For coinductive types, add lazy_ factory method. lazy_ accepts
         std::function<T()> and adapts it to std::function<variant_t()>
         for the lazy constructor.  Returns T (value type). *)
      let lazy_factory =
        if is_coinductive then
          let lazy_name = Id.of_string "lazy_" in
          let thunk_param_ty = Tfun ([], self_ty) in
          let params = [(Id.of_string "thunk", thunk_param_ty)] in
          let variant_t_ty = Tid (Id.of_string "variant_t", []) in
          let adapter_lambda =
            CPPlambda
              ( [],
                Some variant_t_ty,
                [
                  Sasgn
                    ( Id.of_string "_tmp",
                      Some self_ty,
                      CPPfun_call (CPPvar (Id.of_string "thunk"), []) );
                  Sreturn
                    (Some
                       (CPPfun_call
                          ( CPPmember
                              ( CPPvar (Id.of_string "_tmp"),
                                Id.of_string "v" ),
                            [] ) ) );
                ],
                true )
          in
          let thunk_arg =
            CPPfun_call
              ( CPPvar (Id.of_string_soft "std::function<variant_t()>"),
                [adapter_lambda] )
          in
          let ctor_expr =
            CPPfun_call (mk_cppglob name ty_vars, [thunk_arg])
          in
          let body = [Sreturn (Some ctor_expr)] in
          [
            ( Ffundef (lazy_name, Tmod (TMstatic, self_ty), params, body),
              VPublic,
              SCreators );
          ]
        else
          []
      in

      let value_copy_clone_methods =
        if is_coinductive then
          []
        else
          let clone_id = Id.of_string "clone" in
          let d_v_id = Id.of_string "d_v_" in
          let other_id = Id.of_string "_other" in
          let rec is_direct_self_ref = function
            | Miniml.Tglob (r, args, _) ->
              Environ.QGlobRef.equal Environ.empty_env r name
              && List.length args = List.length vars
              && List.for_all
                   (fun (j, arg) ->
                     match arg with
                     | Miniml.Tvar k | Miniml.Tvar' k -> k = j + 1
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar k)}
                     | Miniml.Tmeta {contents = Some (Miniml.Tvar' k)} ->
                       k = j + 1
                     | _ -> false)
                   (List.mapi (fun j a -> (j, a)) args)
            | Miniml.Tmeta {contents = Some t} -> is_direct_self_ref t
            | _ -> false
          in
          let mk_clone_branches target_tvar_ids target_cpp_tys =
            Array.to_list
              (Array.mapi
                 (fun i tys_list ->
                   let c = cnames.(i) in
                   let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                   let ctor_struct_name =
                     ctor_struct_name_of_ref ~fallback_idx:i c
                   in
                   let field_bindings =
                     List.mapi
                       (fun j ty ->
                         let field_id = lookup_ctor_field_name ctor_struct_name j in
                         let cpp_ty =
                           convert_ml_type_to_cpp_type
                             (empty_env ())
                             (Refset'.add name Refset'.empty)
                             vars
                             ty
                         in
                         let cpp_ty =
                           if ml_type_has_nested_self_ref ~ind_ref:name ty
                           then
                             if is_coinductive then Tshared_ptr cpp_ty
                             else if ml_self_ref_is_uniform ~ind_ref:name ~cname:c ty
                             then Tunique_ptr cpp_ty
                             else Tshared_ptr cpp_ty
                           else cpp_ty
                         in
                         let cpp_ty =
                           if vars = [] then tvar_erase_type cpp_ty else cpp_ty
                         in
                         (field_id, cpp_ty, true))
                       tys_list
                   in
                   let target_field_tys =
                     List.map
                       (fun ty ->
                         let cpp_ty =
                           convert_ml_type_to_cpp_type
                             (empty_env ())
                             (Refset'.add name Refset'.empty)
                             target_tvar_ids
                             ty
                         in
                         let cpp_ty =
                           if ml_type_has_nested_self_ref ~ind_ref:name ty
                           then
                             if is_coinductive then Tshared_ptr cpp_ty
                             else if ml_self_ref_is_uniform ~ind_ref:name ~cname:c ty
                             then Tunique_ptr cpp_ty
                             else Tshared_ptr cpp_ty
                           else cpp_ty
                         in
                         if target_tvar_ids = [] then tvar_erase_type cpp_ty
                         else cpp_ty)
                       tys_list
                   in
                   let ctor_args =
                     List.map2
                       (fun (field_id, source_field_ty, _) target_field_ty ->
                         gen_clone_field_expr
                           ~src_ty:source_field_ty ~dst_ty:target_field_ty
                           (CPPvar field_id))
                       field_bindings
                       target_field_tys
                   in
                   let ctor_id =
                     if List.length target_tvar_ids = List.length vars
                        && List.for_all2 Id.equal target_tvar_ids vars
                     then cname_id
                     else
                       Id.of_string_soft
                         ("typename "
                         ^ render_cpp_type_for_raw_template
                             ~no_custom_inductives:(Refset'.add name Refset'.empty)
                             (Tglob (name, target_cpp_tys, []))
                         ^ "::"
                         ^ Id.to_string cname_id)
                   in
                   let ctor_struct = CPPstruct_id (ctor_id, [], ctor_args) in
                   {
                     smb_scrutinee =
                       CPPfun_call
                         (CPPmember (CPPderef CPPthis, Id.of_string "v"), []);
                     smb_ctor_type = Tid (cname_id, []);
                     smb_var =
                       (match field_bindings with
                       | [] -> None
                       | _ -> Some (Id.of_string ("_clone" ^ string_of_int i)));
                     smb_field_bindings = field_bindings;
                     smb_extra_conds = [];
                     smb_reuse = None;
                     smb_is_value_type = true;
                     smb_is_owned = false;
                     smb_body =
                       [ Sreturn
                           (Some
                              (CPPfun_call
                                 ( mk_cppglob name target_cpp_tys,
                                   [ctor_struct] ))) ];
                   })
                 tys)
          in
          let has_direct_self_ref =
            Array.exists (List.exists is_direct_self_ref) tys
          in
          let clone_method =
            if has_direct_self_ref then
              let clone_field_expr source_field_ty target_field_ty field_s =
                match
                  render_cpp_expr_simple
                    (gen_clone_field_expr
                       ~src_ty:source_field_ty
                       ~dst_ty:target_field_ty
                       (CPPraw ("_alt." ^ field_s)))
                with
                | Some s -> s
                | None -> "_alt." ^ field_s
              in
              let branch_lines =
                Array.to_list
                  (Array.mapi
                     (fun i tys_list ->
                       let c = cnames.(i) in
                       let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                       let ctor_struct_name =
                         ctor_struct_name_of_ref ~fallback_idx:i c
                       in
                       let ctor_s = Id.to_string cname_id in
                       let fields =
                         List.mapi
                           (fun j ty ->
                             let field_id =
                               lookup_ctor_field_name ctor_struct_name j
                             in
                             let source_ty =
                               convert_ml_type_to_cpp_type
                                 (empty_env ())
                                 (Refset'.add name Refset'.empty)
                                 vars
                                 ty
                             in
                             let source_ty =
                               if ml_type_has_nested_self_ref ~ind_ref:name ty
                               then
                                 if is_direct_self_ref ty then
                                   Tunique_ptr source_ty
                                 else if is_coinductive then Tshared_ptr source_ty
                                 else if
                                   ml_self_ref_is_uniform ~ind_ref:name ~cname:c ty
                                 then Tunique_ptr source_ty
                                 else Tshared_ptr source_ty
                               else source_ty
                             in
                             let source_ty =
                               if vars = [] then tvar_erase_type source_ty else source_ty
                             in
                             let target_ty = source_ty in
                             (field_id, ty, source_ty, target_ty))
                           tys_list
                       in
                       let ctor_args =
                         List.map
                           (fun (field_id, ml_ty, source_ty, target_ty) ->
                             let field_s = Id.to_string field_id in
                             if is_direct_self_ref ml_ty then
                               "_alt." ^ field_s
                               ^ " ? std::make_unique<%SELF%>() : nullptr"
                             else
                               clone_field_expr source_ty target_ty field_s)
                           fields
                       in
                       let assign =
                         "      _dst->d_v_ = " ^ ctor_s ^ "{"
                         ^ String.concat ", " ctor_args ^ "};"
                       in
                       let recursive_fields =
                         List.filter_map
                           (fun (field_id, ml_ty, _, _) ->
                             if is_direct_self_ref ml_ty then
                               Some (Id.to_string field_id)
                             else None)
                           fields
                       in
                       let body =
                         match recursive_fields with
                         | [] -> [assign]
                         | rec_fields ->
                           assign
                           :: ("      auto &_dst_alt = std::get<" ^ ctor_s
                               ^ ">(_dst->d_v_);")
                           :: List.map
                                (fun field ->
                                  "      if (_alt." ^ field
                                  ^ ") _stack.push_back({_alt." ^ field
                                  ^ ".get(), _dst_alt." ^ field ^ ".get()});")
                                rec_fields
                       in
                       (ctor_s, body))
                     tys)
              in
              let branch_pp =
                List.mapi
                  (fun idx (ctor_s, body) ->
                    let prefix =
                      if idx = 0 then
                        "    if (std::holds_alternative<" ^ ctor_s
                        ^ ">(_src->v())) {"
                      else if idx = List.length branch_lines - 1 then
                        "    } else {"
                      else
                        "    } else if (std::holds_alternative<" ^ ctor_s
                        ^ ">(_src->v())) {"
                    in
                    let bind =
                      "      const auto &_alt = std::get<" ^ ctor_s
                      ^ ">(_src->v());"
                    in
                    String.concat "\n" (prefix :: bind :: body))
                  branch_lines
              in
              let body =
                String.concat "\n"
                  (["%SELF% clone() const {";
                    "  %SELF% _out{};";
                    "  struct _CloneFrame {";
                    "    const %SELF% *_src;";
                    "    %SELF% *_dst;";
                    "  };";
                    "  std::vector<_CloneFrame> _stack;";
                    "  _stack.push_back({this, &_out});";
                    "  while (!_stack.empty()) {";
                    "    auto _frame = _stack.back();";
                    "    _stack.pop_back();";
                    "    const %SELF% *_src = _frame._src;";
                    "    %SELF% *_dst = _frame._dst;"]
                   @ branch_pp
                   @ ["    }";
                      "  }";
                      "  return _out;";
                      "}"])
              in
              (Fraw body, VPublic, SAccessors)
            else
              ( Fmethod
                  {
                    mf_name = clone_id;
                    mf_tparams = [];
                    mf_ret_type = self_ty;
                    mf_params = [];
                    mf_body = [Smatch (mk_clone_branches vars ty_vars, None)];
                    mf_is_const = true;
                    mf_is_static = false;
                    mf_is_inline = false;
                    mf_this_pos = 0;
                    mf_no_pure = true;
                  },
                VPublic,
                SAccessors )
	          in
          let copy_ctor =
            let cloned_v =
              CPPmember
                ( CPPfun_call
                    (CPPmember (CPPvar other_id, clone_id), []),
                  d_v_id )
            in
            ( Fconstructor
                ( [ (other_id, Tref (Tmod (TMconst, self_ty))) ],
                  [(d_v_id, CPPmove cloned_v)],
                  false ),
              VPublic,
              SCreators )
          in
          let move_ctor =
            ( Fconstructor
                ( [(other_id, Tref (Tref self_ty))],
                  [(d_v_id, CPPmove (CPPmember (CPPvar other_id, d_v_id)))],
                  false ),
              VPublic,
              SCreators )
          in
          let copy_assign =
            ( Fmethod
                {
                  mf_name = Id.of_string_soft "operator=";
                  mf_tparams = [];
                  mf_ret_type = Tref self_ty;
                  mf_params = [(other_id, Tref (Tmod (TMconst, self_ty)))];
                  mf_body =
                    [
                      Sasgn (d_v_id, None,
                        CPPmove (CPPmember
                          (CPPfun_call
                            (CPPmember (CPPvar other_id, clone_id), []),
                           d_v_id)));
                      Sreturn (Some (CPPraw "*this"));
                    ];
                  mf_is_const = false;
                  mf_is_static = false;
                  mf_is_inline = false;
                  mf_this_pos = 0;
                  mf_no_pure = true;
                },
              VPublic,
              SCreators )
          in
          let move_assign =
            ( Fmethod
                {
                  mf_name = Id.of_string_soft "operator=";
                  mf_tparams = [];
                  mf_ret_type = Tref self_ty;
                  mf_params = [(other_id, Tref (Tref self_ty))];
                  mf_body =
                    [
                      Sasgn (d_v_id, None,
                        CPPmove (CPPmember (CPPvar other_id, d_v_id)));
                      Sreturn (Some (CPPraw "*this"));
                    ];
                  mf_is_const = false;
                  mf_is_static = false;
                  mf_is_inline = false;
                  mf_this_pos = 0;
                  mf_no_pure = true;
                },
              VPublic,
              SCreators )
          in
          (* Converting constructor for polymorphic types.
             template <typename _U>
             explicit List(const List<_U>& _other) { ... }
             Enables type conversion between different element type
             instantiations, replacing the old clone_as method. *)
          let converting_ctor =
            let all_fields_empty =
              Array.for_all (fun tys_list -> tys_list = []) tys
            in
            if vars = [] || all_fields_empty then []
            else
              let render_ty ty =
                render_cpp_type_for_raw_template
                  ~no_custom_inductives:(Refset'.add name Refset'.empty)
                  (qualify_inductives
                     ~skip:(fun g -> GlobRef.CanOrd.equal g name)
                     ty)
              in
              let n_vars = List.length vars in
              let u_var_names =
                List.mapi
                  (fun i _ ->
                    Id.of_string
                      (if n_vars = 1 then "_U"
                       else "_U" ^ string_of_int i))
                  vars
              in
              let u_tys =
                List.mapi (fun i x -> Tvar (i, Some x)) u_var_names
              in
              let source_ty = Tglob (name, u_tys, []) in
              let source_type_s = render_ty source_ty in
              let struct_local_name = "%SELF%" in
              let template_params =
                String.concat ", "
                  (List.map
                     (fun u -> "typename " ^ Id.to_string u)
                     u_var_names)
              in
              let n_ctors = Array.length cnames in
              let gen_branch i tys_list =
                let c = cnames.(i) in
                let cname_id = ctor_struct_id_of_ref ~fallback_idx:i c in
                let ctor_struct_name =
                  ctor_struct_name_of_ref ~fallback_idx:i c
                in
                let cname_s = Id.to_string cname_id in
                let source_ctor_s =
                  "typename " ^ source_type_s ^ "::" ^ cname_s
                in
                let field_info =
                  List.mapi
                    (fun j ty ->
                      let field_id =
                        lookup_ctor_field_name ctor_struct_name j
                      in
                      let wrap_nested cpp_ty =
                        if ml_type_has_nested_self_ref ~ind_ref:name ty
                        then
                          if is_coinductive then Tshared_ptr cpp_ty
                          else if ml_self_ref_is_uniform ~ind_ref:name ~cname:c ty
                          then Tunique_ptr cpp_ty
                          else Tshared_ptr cpp_ty
                        else cpp_ty
                      in
                      let src_fty =
                        wrap_nested
                          (convert_ml_type_to_cpp_type (empty_env ())
                             (Refset'.add name Refset'.empty)
                             u_var_names ty)
                      in
                      let dst_fty =
                        wrap_nested
                          (convert_ml_type_to_cpp_type (empty_env ())
                             (Refset'.add name Refset'.empty)
                             vars ty)
                      in
                      (field_id, src_fty, dst_fty))
                    tys_list
                in
                let convert_field (field_id, src_fty, dst_fty) =
                  let field_s = Id.to_string field_id in
                  if src_fty = dst_fty then
                    match src_fty with
                    | Tunique_ptr inner ->
                      (* unique_ptr<T>: null-safe clone via ->clone() *)
                      let inner_s = render_ty inner in
                      field_s ^ " ? std::make_unique<" ^ inner_s ^ ">("
                      ^ field_s ^ "->clone()) : nullptr"
                    | Tglob (g, [Tunique_ptr inner], _)
                      when is_option_global g ->
                      (* optional<unique_ptr<T>>: element-wise clone *)
                      let inner_s = render_ty inner in
                      field_s ^ ".has_value() ? std::make_optional("
                      ^ "std::make_unique<" ^ inner_s ^ ">((*" ^ field_s
                      ^ ")->clone())) : std::nullopt"
                    | Tglob (g, [Tshared_ptr inner], _)
                      when is_option_global g ->
                      (* optional<shared_ptr<T>>: element-wise clone *)
                      let inner_s = render_ty inner in
                      field_s ^ ".has_value() ? std::make_optional("
                      ^ "std::make_shared<" ^ inner_s ^ ">((*" ^ field_s
                      ^ ")->clone())) : std::nullopt"
                    | Tglob (GlobRef.IndRef _ as g, _, _)
                      when not (Table.is_inline_custom g)
                           && not (Table.is_enum_inductive g) ->
                      (* Crane-generated inductive struct: always has clone() *)
                      field_s ^ ".clone()"
                    | _ ->
                      (* Type variables, scalars, shared_ptr, type aliases, etc.:
                         plain copy.  Copy ctor deep-copies for Crane types. *)
                      field_s
                  else
                    match (src_fty, dst_fty) with
                    | Tunique_ptr _, Tunique_ptr dst_inner ->
                      let dst_inner_s = render_ty dst_inner in
                      field_s ^ " ? std::make_unique<" ^ dst_inner_s
                      ^ ">(*" ^ field_s ^ ") : nullptr"
                    | Tglob (g1, [src_inner_ty], _), Tglob (g2, [dst_inner], _)
                      when GlobRef.CanOrd.equal g1 g2 && is_option_global g1
                           && (match src_inner_ty with
                               | Tunique_ptr _ | Tshared_ptr _ -> true
                               | _ -> false)
                           && (match dst_inner with
                               | Tunique_ptr _ | Tshared_ptr _ -> false
                               | _ -> true) ->
                      (* optional<unique_ptr/shared_ptr<T>> → optional<T>:
                         clone the pointed-to value (direct copy is deleted
                         when T itself contains a unique_ptr field). *)
                      let dst_inner_s = render_ty dst_inner in
                      field_s ^ ".has_value() ? std::make_optional<"
                      ^ dst_inner_s ^ ">((*" ^ field_s ^ ")->clone()) : std::nullopt"
                    | Tglob (g1, [src_inner], _), Tglob (g2, [Tunique_ptr dst_inner], _)
                      when GlobRef.CanOrd.equal g1 g2 && is_option_global g1
                           && (match src_inner with
                               | Tunique_ptr _ | Tshared_ptr _ -> false
                               | _ -> true) ->
                      (* optional<T> → optional<unique_ptr<T>> *)
                      let dst_inner_s = render_ty dst_inner in
                      field_s ^ ".has_value() ? std::make_optional(std::make_unique<"
                      ^ dst_inner_s ^ ">((*" ^ field_s ^ ").clone())) : std::nullopt"
                    | Tglob (g1, [src_inner], _), Tglob (g2, [Tshared_ptr dst_inner], _)
                      when GlobRef.CanOrd.equal g1 g2 && is_option_global g1
                           && (match src_inner with
                               | Tunique_ptr _ | Tshared_ptr _ -> false
                               | _ -> true) ->
                      (* optional<T> → optional<shared_ptr<T>> *)
                      let dst_inner_s = render_ty dst_inner in
                      field_s ^ ".has_value() ? std::make_optional(std::make_shared<"
                      ^ dst_inner_s ^ ">((*" ^ field_s ^ ").clone())) : std::nullopt"
                    | Tglob (g1, _, _), Tglob (g2, _, _)
                      when GlobRef.CanOrd.equal g1 g2 ->
                      render_ty dst_fty ^ "(" ^ field_s ^ ")"
                    | (Tvar _ | Tauto), _ | _, (Tvar _ | Tauto) ->
                      (* Type variable conversion: converting constructor *)
                      render_ty dst_fty ^ "(" ^ field_s ^ ")"
                    | _ when contains_tvar dst_fty || contains_tvar src_fty ->
                      (* Contains type variable: converting constructor *)
                      render_ty dst_fty ^ "(" ^ field_s ^ ")"
                    | _ ->
                      (* Fully concrete, different: converting constructor *)
                      render_ty dst_fty ^ "(" ^ field_s ^ ")"
                in
                ( source_ctor_s,
                  cname_s,
                  field_info,
                  List.map convert_field field_info )
              in
              let branches =
                List.init n_ctors (fun i -> gen_branch i tys.(i))
              in
              let buf = Buffer.create 256 in
              Buffer.add_string buf
                ("template <" ^ template_params ^ ">\n");
              Buffer.add_string buf
                ("explicit " ^ struct_local_name ^ "(const "
                 ^ source_type_s ^ "& _other) {\n");
              if n_ctors = 1 then begin
                let source_ctor_s, cname_s, field_info, converted =
                  List.hd branches
                in
                match field_info with
                | [] ->
                  Buffer.add_string buf
                    ("  d_v_ = " ^ cname_s ^ "{};\n")
                | _ ->
                  let bindings =
                    String.concat ", "
                      (List.map
                         (fun (id, _, _) -> Id.to_string id)
                         field_info)
                  in
                  Buffer.add_string buf
                    ("  const auto& [" ^ bindings
                     ^ "] = std::get<" ^ source_ctor_s
                     ^ ">(_other.v());\n");
                  Buffer.add_string buf
                    ("  d_v_ = " ^ cname_s ^ "{"
                     ^ String.concat ", " converted ^ "};\n")
              end
              else begin
                List.iteri
                  (fun idx
                       (source_ctor_s, cname_s, field_info, converted) ->
                    let is_last = idx = n_ctors - 1 in
                    if idx = 0 then
                      Buffer.add_string buf
                        ("  if (std::holds_alternative<" ^ source_ctor_s
                         ^ ">(_other.v())) {\n")
                    else if is_last then
                      Buffer.add_string buf "  } else {\n"
                    else
                      Buffer.add_string buf
                        ("  } else if (std::holds_alternative<"
                         ^ source_ctor_s ^ ">(_other.v())) {\n");
                    match field_info with
                    | [] ->
                      Buffer.add_string buf
                        ("    d_v_ = " ^ cname_s ^ "{};\n")
                    | _ ->
                      let bindings =
                        String.concat ", "
                          (List.map
                             (fun (id, _, _) -> Id.to_string id)
                             field_info)
                      in
                      Buffer.add_string buf
                        ("    const auto& [" ^ bindings
                         ^ "] = std::get<" ^ source_ctor_s
                         ^ ">(_other.v());\n");
                      Buffer.add_string buf
                        ("    d_v_ = " ^ cname_s ^ "{"
                         ^ String.concat ", " converted ^ "};\n"))
                  branches;
                Buffer.add_string buf "  }\n"
              end;
              Buffer.add_string buf "}";
              [(Fraw (Buffer.contents buf), VPublic, SCreators)]
          in
          [copy_ctor; move_ctor; copy_assign; move_assign; clone_method]
          @ converting_ctor
      in

      (* Add public accessor for v_ to enable pattern matching from outside *)
      let v_accessor =
        if is_coinductive then
          (* For coinductive: const variant_t& v() const { return
             lazy_v_.force(); } *)
          ( Fmethod
              {
                mf_name = Id.of_string "v";
                mf_tparams = [];
                mf_ret_type =
                  Tmod (TMconst, Tref (Tid (Id.of_string "variant_t", [])));
                mf_params = [];
                mf_body =
                  [
                    Sreturn
                      (Some
                         (CPPfun_call
                            ( CPPmember
                                ( CPPvar (Id.of_string "d_lazyV_"),
                                  Id.of_string "force" ),
                              [] ) ) );
                  ];
                mf_is_const = true;
                mf_is_static = false;
                mf_is_inline = false;
                mf_this_pos = 0;
                mf_no_pure = false;
              },
            VPublic,
            SAccessors )
        else (* For inductive: const variant_t& v() const { return v_; } *)
          ( Fmethod
              {
                mf_name = Id.of_string "v";
                mf_tparams = [];
                mf_ret_type =
                  Tmod (TMconst, Tref (Tid (Id.of_string "variant_t", [])));
                mf_params = [];
                mf_body = [Sreturn (Some (CPPvar (Id.of_string "d_v_")))];
                mf_is_const = true;
                mf_is_static = false;
                mf_is_inline = false;
                mf_this_pos = 0;
                mf_no_pure = false;
              },
            VPublic,
            SAccessors )
      in

      (* Add mutable accessor for reuse optimization (Phase 3). For
         non-coinductive types: variant_t& v_mut() { return v_; } Not generated
         for coinductive types (lazy evaluation complicates reuse). *)
      let v_mut_accessor =
        if is_coinductive then
          []
        else
          [
            ( Fmethod
                {
                  mf_name = Id.of_string "v_mut";
                  mf_tparams = [];
                  mf_ret_type = Tref (Tid (Id.of_string "variant_t", []));
                  mf_params = [];
                  mf_body = [Sreturn (Some (CPPvar (Id.of_string "d_v_")))];
                  mf_is_const = false;
                  mf_is_static = false;
                  mf_is_inline = true;
                  mf_this_pos = 0;
                  mf_no_pure = true;
                },
              VPublic,
              SManipulators );
          ]
      in

      (* 6. Generate methods from method candidates using shared helper *)
      let method_fields =
        List.map (gen_single_method name vars) method_candidates
      in

      (* Detect if any method contains shared_from_this (i.e., returns 'this').
         If so, the struct needs to inherit from
         std::enable_shared_from_this. *)
      let needs_shared_from_this =
        List.exists
          (fun (fld, _vis, _tag) ->
            match fld with
            | Fmethod {mf_body; _} ->
              List.exists stmt_has_shared_from_this mf_body
            | _ -> false )
          method_fields
      in

      (* Categorize user methods: const methods are ACCESSORS, non-const are
         MANIPULATORS *)
      let method_fields =
        List.map
          (fun (fld, vis, _tag) ->
            match fld with
            | Fmethod {mf_is_const = true; _} -> (fld, vis, SAccessors)
            | Fmethod _ -> (fld, vis, SManipulators)
            | _ -> (fld, vis, SNoTag) )
          method_fields
      in
      (* Split methods into manipulators and accessors *)
      let method_manipulators =
        List.filter (fun (_, _, tag) -> tag = SManipulators) method_fields
      in
      let method_accessors =
        List.filter (fun (_, _, tag) -> tag <> SManipulators) method_fields
      in

      (* BDE field ordering: public: constructor structs, variant_using (TYPES)
         private: variant_member (DATA)
         public: public_ctors + lazy_ctor + factory methods (CREATORS),
         v_mut + manipulators (MANIPULATORS),
         v_accessor + const methods (ACCESSORS) *)
      let all_fields =
        constructor_structs
        @ [variant_using]
        @ element_using
        @ [variant_member]
        @ default_ctor
        @ public_ctors
        @ value_copy_clone_methods
        @ lazy_ctor
        @ factory_methods
        @ lazy_factory
        @ iterative_destructor
        @ v_mut_accessor
        @ method_manipulators
        @ [v_accessor]
        @ method_accessors
      in

      (* Just the struct itself - no extra namespace wrapper *)
      Dstruct
        {
          ds_ref = name;
          ds_fields = all_fields;
          ds_tparams = templates;
          ds_constraint = None;
          ds_needs_shared_from_this = needs_shared_from_this;
        }

(** Generate methods for eponymous records. Uses the shared gen_single_method
    helper for records where methods are generated directly on the module struct
    (which has record fields merged). name: the record's GlobRef (e.g., IndRef
    for CHT) vars: the type variables of the record (e.g., [K; V] for CHT<K, V>)
    method_candidates: list of (func_ref, body, type, this_position) tuples *)
let gen_record_methods (name : GlobRef.t) (vars : Id.t list) method_candidates =
  List.map (gen_single_method name vars) method_candidates
