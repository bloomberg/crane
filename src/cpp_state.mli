(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** This module holds the mutable, per-extraction rendering state and registries
   shared across the C++ pretty-printers. It owns the current render context
   ([render_ctx], with save/restore snapshots), the method and name-resolution
   registries, the [std::]-namespace name configuration ([std_names]),
   eponymous-record tracking, and the wrapper/collision/global-scope tables.
   Much of the surface is intentionally mutable global state (refs and
   hashtables) that is reset between extraction units via [reset_cpp_state]. *)

(** {2 Layout combinators} *)

(** Trivial box combinators used by the pretty-printers. *)
val h : 'a -> 'a

(** Shadows [Pp.v]: returns its second argument unchanged, skipping vertical box
    construction (output is reformatted by clang-format anyway). *)
val v : 'a -> 'b -> 'b

(** Shadows [Pp.hov]: returns its second argument unchanged, skipping
    horizontal-or-vertical box construction. *)
val hov : 'a -> 'b -> 'b

(** {2 Method registry} *)

(** Per-run and global method registries plus their accessors. *)
val method_registry : Method_registry.t option ref

(** Pre-built registry from the full [ml_structure], used in separate extraction
    so cross-module method calls are recognised. [None] when unset; cleared by
    [reset_cpp_state]. *)
val global_method_registry : Method_registry.t option ref

(** Set [global_method_registry] to [Some] the given registry. *)
val set_global_method_registry : Method_registry.t -> unit

(** Reset [global_method_registry] to [None]. *)
val clear_global_method_registry : unit -> unit

(** Return the contents of [method_registry].
    @raise CErrors.Anomaly if the registry has not been initialized. *)
val get_method_registry : unit -> Method_registry.t

(** {2 Name resolution} *)

(** Name-resolution cache and its accessor. *)
val name_cache : Name_resolution.t option ref

(** Return the contents of [name_cache].
    @raise CErrors.Anomaly if the cache has not been initialized. *)
val get_name_cache : unit -> Name_resolution.t

(** Pretty-printers for type variables and parameter lists. *)
val pp_tvar : Names.variable -> Pp.t

(** Print type variables as a boxed tuple, followed by a space when the list is
    non-empty. *)
val pp_parameters : Names.variable list -> Pp.t

(** Print already-rendered parameter strings as a boxed tuple, followed by a
    space when the list is non-empty. *)
val pp_string_parameters : string list -> Pp.t

(** Look up a custom type rendering for a global reference, if any. *)
val find_type_custom_opt : Names.GlobRef.t -> (string list * string) option

(** Reserved C++ keywords that identifiers must avoid. *)
val keywords : Names.Id.Set.t

(** {2 Output modules} *)

(** Set of module paths that are valid extraction outputs. *)
val valid_output_modules : (Names.module_path, unit) Hashtbl.t

(** Replace the contents of [valid_output_modules] with the given module paths;
    afterwards only those modules yield [#include] lines from [pp_open]. *)
val set_valid_output_modules : Names.module_path list -> unit

(** Empty [valid_output_modules], re-enabling [#include] emission for every
    module. *)
val clear_valid_output_modules : unit -> unit

(** {2 Wrappers} *)

(** Global registry of wrapper names that were not merged. *)
val global_unmerged_wrappers : (string, unit) Hashtbl.t

(** Record that the given wrapper struct name must stay unmerged across
    extraction passes, so references use the qualified form. *)
val mark_global_unmerged : string -> unit

(** [true] if the wrapper struct name was marked by [mark_global_unmerged]. *)
val is_global_unmerged : string -> bool

(** Empty [global_unmerged_wrappers]. *)
val clear_global_unmerged : unit -> unit

(** {2 Preamble} *)

(** Pretty-printers for includes, comments, and file preambles. *)
val pp_open : Names.module_path -> Pp.t

(** Wrap the given document in OCaml-style comment delimiters [(* ... *)]. *)
val pp_comment : Pp.t -> Pp.t

(** Print an optional header comment followed by a blank line; empty for
    [None]. *)
val pp_header_comment : Pp.t option -> Pp.t

(** Append a newline to the document unless it is empty. *)
val then_nl : Pp.t -> Pp.t

(** Build the preamble of an implementation file: the optional header comment
    followed by one [pp_open] line per used module. The first and last
    arguments are ignored. *)
val preamble : 'a -> Pp.t option -> Names.module_path list -> 'b -> Pp.t

(** Build the preamble of a header/signature file; currently identical to
    [preamble]. *)
val sig_preamble : 'a -> Pp.t option -> Names.module_path list -> 'b -> Pp.t

(** {2 Render context} *)

(** Mutable current render context threaded through the pretty-printers. *)
type render_ctx = {
  mutable rc_in_struct : bool;
  mutable rc_concepts_hoisted : bool;
  mutable rc_struct_name : Pp.t option;
  mutable rc_struct_mp : Names.module_path option;
  mutable rc_in_template : bool;
  mutable rc_in_meyers_body : bool;
}

(** The single global render context, mutated in place during rendering and
    reset by [reset_cpp_state]. *)
val render_ctx : render_ctx

(** Concept definitions hoisted out of the current struct. *)
val hoisted_concept_defs : Pp.t list ref

(** Immutable snapshot of a [render_ctx] for save/restore. *)
type render_ctx_snapshot = {
  rcs_in_struct : bool;
  rcs_concepts_hoisted : bool;
  rcs_struct_name : Pp.t option;
  rcs_struct_mp : Names.module_path option;
  rcs_in_template : bool;
  rcs_in_meyers_body : bool;
}

(** Capture the current fields of [render_ctx] as a snapshot. *)
val save_render_ctx : unit -> render_ctx_snapshot

(** Overwrite every field of [render_ctx] from the snapshot. *)
val restore_render_ctx : render_ctx_snapshot -> unit

(** Run a rendering computation under a temporarily modified context.
    @param setup mutates [render_ctx] before the computation runs
    @return the computation's result, with the previous context restored *)
val with_render_ctx : setup:(unit -> unit) -> (unit -> 'a) -> 'a

(** {2 Template static accessors} *)

(** Tracking for template static accessor labels and their kernel names. *)
val template_static_accessors : (Names.module_path * Names.Label.t) list ref

(** Canonical kernel names of template static accessors, for cross-functor
    matching. Cleared by [reset_cpp_state]. *)
val template_static_accessor_kns : (Names.KerName.t, unit) Hashtbl.t

(** Labels also used by non-Meyers-singleton definitions, so that label-only
    fallback matching does not produce false positives. Cleared by
    [reset_cpp_state]. *)
val non_accessor_labels : (Names.Label.t, unit) Hashtbl.t

(** Record the definition at the given module path and label as a template
    static accessor (Meyers singleton), by prepending it to
    [template_static_accessors]. *)
val register_template_static_accessor :
  Names.module_path -> Names.Label.t -> unit

(** Map from functor-application module paths to their source module. *)
val functor_app_sources : (Names.module_path, Names.module_path) Hashtbl.t

(** {2 Eponymous records} *)

(** In-flight state used while emitting an eponymous record. *)
val eponymous_type_ref : Names.GlobRef.t option ref

(** Set during module rendering when the eponymous inductive should be promoted
    into the module struct; [cpp_ind.ml] then renders its fields flat instead of
    inside a wrapping struct. Reset to [None] by [reset_cpp_state]. *)
val eponymous_promote_ref : Names.GlobRef.t option ref

(** Accumulated non-inductive definitions to emit at file scope after the
    promoted template struct. Reset to empty by [reset_cpp_state]. *)
val eponymous_deferred : Pp.t ref

(** Whether the promoted inductive needs [enable_shared_from_this]; set while
    rendering flat in [cpp_ind.ml] and consumed by the [MEstruct] wrapper in
    [cpp.ml]. Reset to [false] by [reset_cpp_state]. *)
val eponymous_promote_sft : bool ref

(** Method candidates collected for the current eponymous type, as
    [(function_ref, body, type, this_position)] where [this_position] is the
    0-based index of the first argument matching the eponymous type. Reset to
    [[]] by [reset_cpp_state]. *)
val method_candidates :
  (Names.GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int) list ref

(** The eponymous record of the module being rendered, as
    [(record_ref, field_refs, ind_packet)], whose fields are merged into the
    module struct. Reset to [None] by [reset_cpp_state]. *)
val eponymous_record :
  (Names.GlobRef.t * Names.GlobRef.t option list * Miniml.ml_ind_packet)
  option ref

(** {2 std:: names} *)

(** Configurable names for the [std::] symbols emitted by the extractor. *)
type std_names = {
  shared_ptr : string;
  make_shared : string;
  visit : string;
  move : string;
  forward : string;
  any_cast : string;
  logic_error : string;
  overloaded : string;
  ns : string;
  str_suffix : string;
  same_as : string;
  declval : string;
  convertible_to : string;
  holds_alternative : string;
  get_if : string;
  get : string;
  enable_from_this : string;
}

(** The plain [std::] flavor of {!std_names} (with ["Overloaded"] and the ["s"]
    string-literal suffix). *)
val default_std_names : std_names

(** The names in effect for the current extraction pass; initialized by
    [init_std_names] and read through [sn]. *)
val std_names : std_names ref

(** Build a name set for a namespace prefix. ["bsl::"] yields the BDE flavor
    (with [bdlf::Overloaded] and the ["_s"] suffix); any other prefix yields
    [default_std_names]. *)
val mk_std_names : string -> std_names

(** Set [std_names] from the current [Table] settings: the BDE flavor when
    [Table.std_lib ()] is ["BDE"], otherwise the [std::] flavor; then, if
    [Table.non_atomic_rc ()], override the smart pointer with [crane::rc] /
    [crane::make_rc] / [crane::enable_rc_from_this]. *)
val init_std_names : unit -> unit

(** Shorthand for [!std_names]. *)
val sn : unit -> std_names

(** Whether an ML type denotes a typeclass instance. *)
val is_typeclass_instance : 'a -> Miniml.ml_type -> bool

(** {2 Wrapper and scope tables} *)

(** Tables tracking wrapper modules, collisions, and global-scope entities. *)
val wrapper_module_table : (Names.module_path, string) Hashtbl.t

(** Module paths that were collision-wrapped (a child module whose name clashes
    with a global inductive, folded into a parent struct); for these,
    [wrapper_qualify_name] strips the child qualifier. Cleared by
    [reset_cpp_state]. *)
val collision_wrapper_table : (Names.module_path, unit) Hashtbl.t

(** Enum inductives rendered at global scope rather than inside a struct, used
    to avoid spurious struct qualification in [.cpp] files. Cleared by
    [reset_cpp_state]. *)
val global_scope_enum_table : (Names.GlobRef.t, unit) Hashtbl.t

(** Type aliases ([Dtype] constants) rendered at global scope as [using T = ...]
    declarations. Populated during rendering by
    [register_global_scope_type_alias], queried for name qualification, and
    cleared by [reset_cpp_state]. *)
val global_scope_type_alias_table : (Names.GlobRef.t, unit) Hashtbl.t

(** Record that the given type alias was rendered at global scope. *)
val register_global_scope_type_alias : Names.GlobRef.t -> unit

(** [true] if the reference is in [global_scope_type_alias_table]. *)
val is_global_scope_type_alias : Names.GlobRef.t -> bool

(** Pre-rendered forward declarations to inject into a [Dnspace] struct, keyed
    by struct name. Cleared by [reset_cpp_state]. *)
val pending_wrapper_decls : (string, Pp.t) Hashtbl.t

(** Wrapper struct names that have pending declarations and therefore cannot be
    merged; consulted when choosing between the merged ([List<A>]) and unmerged
    ([List::list<A>]) name forms. Cleared by [reset_cpp_state]. *)
val unmerged_wrappers : (string, unit) Hashtbl.t

(** What a nested struct name was emitted for: a Rocq reference, or a module
    (which has no [GlobRef.t]). *)
type nested_struct_owner =
  | NSref of Names.GlobRef.t
  | NSmodule of Names.ModPath.t

(** C++ names of structs emitted as members of an enclosing struct, mapped to
    every owner they stand for. A nested struct shadows any global-scope type
    of the same name. Cleared by [reset_cpp_state]. *)
val nested_struct_names : (string, nested_struct_owner list) Hashtbl.t

(** Record that an owner was emitted as a nested struct under the given C++
    name. *)
val add_nested_struct_name : string -> nested_struct_owner -> unit

(** Whether a reference rendered unqualified under the given name is shadowed
    by a nested struct of that name. False for the shadower itself. *)
val is_shadowed_global_name : string -> Names.GlobRef.t -> bool

(** Capitalized inductive names mapped to their module paths across all modules,
    used to detect module/inductive name collisions. Cleared by
    [reset_cpp_state]. *)
val global_inductive_names : (string, Names.module_path) Hashtbl.t

(** Qualify a C++ name with its wrapper struct when the reference's module path
    is a wrapper module. [VarRef] references (lifted declarations) are never
    qualified, and already-qualified names are only rewritten for
    collision-wrapped modules, whose child qualifier is replaced by the wrapper
    struct name.
    @return the possibly-qualified name *)
val wrapper_qualify_name : Names.GlobRef.t -> string -> string

(** {2 Method registration} *)

(** Register and query methods and their any-returning status. *)
val register_method :
  Names.GlobRef.t ->
  Names.GlobRef.t -> int -> ?ind_tvar_positions:int list -> unit -> unit

(** Test whether a function qualifies as a method on an eponymous type (given
    its body and type) and register it if so; single entry point replacing the
    manual argument-position/body-safety/registration sequence.
    @return the resulting candidate, or [None] if it does not qualify *)
val try_register_method :
  Names.GlobRef.t ->
  Names.GlobRef.t ->
  Miniml.ml_ast -> Miniml.ml_type -> Method_registry.method_candidate option

(** Look up a function in the method registry.
    @return [Some (eponymous_type, this_position)] if it is registered as a
      method, [None] otherwise *)
val is_registered_method : Names.GlobRef.t -> (Names.GlobRef.t * int) option

(** Number of value parameters a registered method takes, receiver included;
    [0] when unknown. *)
val lookup_method_arity : Names.GlobRef.t -> int

(** Return the 0-based positions, in a registered method's type-variable list,
    of the inductive's own template parameters — those deducible from the
    receiver and thus omitted from explicit template arguments. *)
val lookup_method_ind_tvar_positions : Names.GlobRef.t -> int list

(** Record in the method registry that the given method returns [std::any] /
    [bsl::any]. *)
val register_method_returns_any : Names.GlobRef.t -> unit

(** [true] if the method was marked by [register_method_returns_any]. *)
val method_returns_any : Names.GlobRef.t -> bool

(** {2 Eponymous record registry} *)

(** Global registry and lookups for eponymous records. *)
val global_eponymous_record_registry : (Names.GlobRef.t, unit) Hashtbl.t

(** Reverse index backing [get_containing_eponymous_struct]: the eponymous
    record declared in each module path (at most one per module). Kept in sync
    by [register_eponymous_record] and cleared by [reset_cpp_state]. *)
val eponymous_record_by_modpath :
  (Names.module_path, Names.GlobRef.t) Hashtbl.t

(** Register an inductive as an eponymous record, adding it to the global
    registry and, for [IndRef]s, to the by-module-path reverse index. *)
val register_eponymous_record : Names.GlobRef.t -> unit

(** [true] if the reference is in [global_eponymous_record_registry]. *)
val is_eponymous_record_global : Names.GlobRef.t -> bool

(** For a constant, return the eponymous record of its containing module, if
    any — used to emit [StructName<Args>::f()] rather than
    [StructName::f<Args>()]. Always [None] for non-[ConstRef] references. *)
val get_containing_eponymous_struct :
  Names.GlobRef.t -> Names.GlobRef.t option

(** Declarations of the structure currently being emitted. *)
val current_structure_decls :
  (Names.Label.t * Miniml.ml_structure_elem) list ref

(** {2 Per-run reset} *)

(** Reset all mutable state between extraction units. *)
val reset_cpp_state : unit -> unit

(** {2 Projections} *)

(** Queries about eponymous-record and suppressed projections, and dfix filtering. *)
val is_eponymous_record_projection : Names.GlobRef.t -> bool

(** [true] for a projection that is not a higher-order projection, and so should
    not be rendered as a standalone function. *)
val is_suppressed_projection : Names.GlobRef.t -> bool

(** Drop from a [Dfix] group the entries that are inline customs, local or
    globally registered method candidates, eponymous-record projections, or
    suppressed projections.
    @return the three input arrays filtered in parallel *)
val filter_dfix :
  Names.GlobRef.t array ->
  'a array -> 'b array -> Names.GlobRef.t array * 'a array * 'b array
