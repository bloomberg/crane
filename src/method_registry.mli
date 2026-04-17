(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** {1 Method Registry}

    Crane translates certain top-level Rocq functions into C++ methods on the
    struct that represents their "eponymous" inductive or record type. For
    example, if module [List] contains an inductive [list] and a function
    [app : list A -> list A -> list A], then [app] becomes a method on the
    [List] struct in C++ rather than a free function.

    A function qualifies as a method when:
    - It lives in the same module as (or a wrapper module of) an eponymous
      inductive type, {b and}
    - One of its arguments has the eponymous type (this becomes the [this]
      parameter), {b and}
    - Its body is "safe" — it does not directly return the first argument, which
      would create an invalid [return this] converting a raw pointer back to
      [shared_ptr].

    This module performs the full method detection scan {i once} over the entire
    [ml_structure] before code generation begins, storing the results in an
    opaque registry. During rendering, [cpp.ml] queries the registry instead of
    re-scanning the AST.

    {2 Lifecycle}

    + [create s] scans the full [ml_structure] to find all methods.
    + [compute_returns_any] (called internally by [create]) determines which
      methods have erased return types that must be rendered as [std::any].
    + During rendering, [lookup] / [is_registered_method] / [method_returns_any]
      are used to query the registry.
    + [register_method] / [register_method_returns_any] allow cpp.ml to add
      late-discovered methods (e.g. from functor applications or module
      processing that is interleaved with rendering). *)

open Names

(** Information about a single registered method. *)
type method_info = {
  epon_ref : GlobRef.t;
      (** The eponymous inductive or record type this method belongs to. For
          example, for [List.app], this would be the [GlobRef] of [list]. *)
  this_pos : int;
      (** 0-based index of the argument that becomes [this]. For
          [app : list A -> list A -> list A], this is [0] because the first
          argument is the receiver. For a function like
          [insert : K -> V -> map K V -> map K V], this would be [2]. *)
  ind_tvar_positions : int list;
      (** Indices into the function's type-variable list that correspond to the
          inductive's template parameters. These type variables are already
          deducible from the receiver type, so they can be omitted from the
          method's own template parameter list.

          Example: for [app : forall A, list A -> list A -> list A], the
          function has type variables [[A]] at position [0]. The inductive
          [list A] also has [A], so [ind_tvar_positions = [0]], meaning template
          parameter 0 is redundant in the method signature. *)
  returns_any : bool;
      (** Whether the method's return type is erased to [std::any]. This happens
          when the return type involves indexed type variables that cannot be
          represented in C++ (the "type erasure" pattern). When true, the method
          signature uses [std::any] as return type and callers must use
          [std::any_cast] to recover the value. *)
}

(** A method candidate: (func_ref, body, type, this_position). Stored during
    pre-scan indexed by the eponymous inductive they belong to, so cpp.ml can
    retrieve them without re-collecting. *)
type method_candidate = GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int

(** Opaque registry type. Internally a hashtable from [GlobRef.t] (the function
    reference) to [method_info], plus a reverse index from inductive [GlobRef.t]
    to its method candidates. *)
type t

(** Build the registry by scanning the full [ml_structure].

    This performs the complete method detection pass:
    + For each module, finds the eponymous inductive (if any) by comparing the
      module name against inductive names (case-insensitive).
    + Scans all [Dterm] and [Dfix] declarations in the same module (and wrapper
      modules) for functions whose type includes the eponymous type as an
      argument.
    + Checks each candidate's body with [body_safe_for_method] to ensure it does
      not directly return the first argument.
    + After all methods are registered, runs [compute_returns_any] to determine
      which methods have erased return types.

    Enum inductives (all-nullary constructors with no type parameters) are
    detected early during this pass and registered via
    [Table.add_enum_inductive], since the method scanner needs to exclude them.
*)
val create : Miniml.ml_structure -> t

(** Look up full method info for a function reference. Returns [None] if the
    function is not a registered method. *)
val lookup : t -> GlobRef.t -> method_info option

(** Convenience: is the function a registered method? Returns
    [Some (epon_ref, this_pos)] if yes, [None] otherwise. Used primarily by the
    topological sort in [Structure_analysis] to add cross-module dependencies
    when a function calls a method defined in another module. *)
val is_registered_method : t -> GlobRef.t -> (GlobRef.t * int) option

(** Return the inductive type-variable positions for a registered method.
    Returns [[]] if the function is not registered. Used by [cpp.ml] to omit
    redundant template parameters from the method's C++ signature (since they
    are deducible from [this]). *)
val lookup_ind_tvar_positions : t -> GlobRef.t -> int list

(** Does this method return [std::any] (erased indexed return type)? Returns
    [false] if the function is not registered. *)
val method_returns_any : t -> GlobRef.t -> bool

(** Return all method candidates for a given inductive type. Returns candidates
    as [(func_ref, body, type, this_position)] tuples. These are collected
    during the pre-scan and can be used directly by cpp.ml to generate method
    bodies without re-scanning the structure. Returns [[]] if no candidates are
    registered. *)
val get_candidates : t -> GlobRef.t -> method_candidate list

(** {2 Mutation interface}

    During rendering, additional methods may be discovered that were not visible
    during the initial scan — for example, methods generated from functor
    applications or from module-level processing in [cpp.ml]. These functions
    allow adding entries to an already-created registry. *)

(** Register a new method after initial creation.
    @param t the registry
    @param func_ref the function being registered as a method
    @param epon_ref the eponymous type it belongs to
    @param this_pos argument index that becomes [this]
    @param ind_tvar_positions type-variable indices deducible from receiver *)
val register_method :
  t -> GlobRef.t -> GlobRef.t -> int -> ind_tvar_positions:int list -> unit

(** Add a method candidate for an inductive after initial creation. Appends the
    candidate to the existing list for that inductive. *)
val add_candidate : t -> GlobRef.t -> method_candidate -> unit

(** Check if [func_ref] qualifies as a method on [epon_ref] and register it
    if so.  Combines [find_epon_arg_pos], [body_safe_for_method],
    [register_method], and [add_candidate] into a single call.

    Returns [Some (func_ref, body, ty, this_pos)] on success, [None] if the
    function does not qualify. *)
val try_register_method :
  t -> GlobRef.t -> GlobRef.t -> Miniml.ml_ast -> Miniml.ml_type ->
  method_candidate option

(** Mark an existing registered method as returning [std::any]. No-op if the
    function is not registered. *)
val register_method_returns_any : t -> GlobRef.t -> unit

(** {2 Body safety check} *)

(** Check if a MiniML function body is safe to turn into a C++ method.

    When a function becomes a method, its first argument is received as a raw
    [this] pointer instead of a [shared_ptr]. If the function body directly
    returns that first argument (i.e. the result is a bare [MLrel] pointing to
    argument 0), the generated C++ would contain [return this] — but [this] is a
    raw pointer and cannot be implicitly converted to [shared_ptr], causing a
    compile error.

    This function returns [true] if the body is safe (does not directly return
    the first argument).

    {b What counts as "direct return":}
    - A bare [MLrel] in tail position that refers to the first argument.
    - This check recurses through [MLcase] branches, [MLletin] bodies, [MLmagic]
      wrappers, and [MLfix] bodies to find all tail positions.

    {b What does NOT count as "direct return" (and is safe):}
    - Using the first argument for field access: [MLproj(arg, field)] translates
      to [this->field].
    - Passing the first argument to another function: [MLapp(f, [arg])]
      translates to [f(this)].
    - Pattern matching on the first argument: [MLcase(arg, ...)] translates to a
      [std::visit] on [this->v()].
    - Wrapping the argument in a constructor: [MLcons(C, [arg])] produces a new
      value.

    @param this_pos  0-based index of the argument becoming [this].
      Defaults to [0]. Must be less than the number of outer lambdas in
      [body]; determines which [MLrel] index is checked for direct return.
    @param ret_has_shared_epon  When [true], relaxes the safety check to
      allow returning [this] wrapped in a constructor whose return type
      contains [shared_ptr] of the eponymous type — the generated C++ will
      use [shared_from_this()] instead of a bare [this]. Defaults to
      [false]. *)
val body_safe_for_method :
  ?this_pos:int -> ?ret_has_shared_epon:bool -> Miniml.ml_ast -> bool

(** Check if the return type of an ML arrow type contains [ref].

    Extracts the return type from a curried [Tarr] chain and recursively checks
    whether [ref] appears anywhere in it (including inside type arguments).

    Used at method registration call sites to determine whether
    [replace_return_this_stmt] will convert [return this] to
    [return shared_from_this()] — when the return type references the eponymous
    inductive, the C++ return type will contain [shared_ptr]. *)
val ml_return_type_has_ref : GlobRef.t -> Miniml.ml_type -> bool

(** {2 Module-level helpers} *)

(** Collect [Dtype] refs from a declaration list that share [modpath],
    excluding inline-custom types.  [extract_decl] extracts [ml_decl option]
    from each list item (handles both [ml_specif] and [ml_structure_elem]). *)
val collect_module_type_aliases :
  extract_decl:('a -> Miniml.ml_decl option) ->
  Names.ModPath.t -> 'a list -> GlobRef.t list

(** {2 Eponymous-type helpers}

    These helpers are also used by [cpp.ml] during rendering when it needs to
    detect eponymous types in modules being processed. *)

(** Find all non-typeclass, non-custom, non-enum, non-mutual inductives in a
    module's declarations.  Returns a list of [GlobRef.t] for each eligible
    inductive packet. *)
val find_all_module_inductives :
  Miniml.ml_module_structure -> GlobRef.t list

(** Find the eponymous inductive in a module's declaration list.

    An inductive is "eponymous" when its lowercase name matches the lowercase
    module name. For example, module [List] contains inductive [list], and
    [String.lowercase_ascii "list" = String.lowercase_ascii "List"].

    Type-class inductives are excluded because they are rendered as C++ concepts
    rather than structs, so methods on them would not make sense.

    Scans only [SEdecl (Dind ...)] entries in the given list; does not recurse
    into sub-modules.

    @param module_name the module name to match against (case-insensitive)
    @param decls the module's declaration list
    @return [Some ind_ref] for the first matching inductive, or [None] *)
val find_eponymous_inductive :
  string -> Miniml.ml_module_structure -> GlobRef.t option

(** Find the position of the first argument whose type matches an eponymous
    inductive reference.

    Walks the curried arrow type [T1 -> T2 -> ... -> Tn -> R] and returns the
    0-based position of the first [Ti] that is [Tglob(epon_ref, ...)]. Also
    extracts the type-variable indices from that argument's type parameters.

    @param epon_ref the inductive to search for
    @param ty the function's MiniML type
    @return [Some (pos, ind_tvar_positions)] or [None] *)
val find_epon_arg_pos : GlobRef.t -> Miniml.ml_type -> (int * int list) option
