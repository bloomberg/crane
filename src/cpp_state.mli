(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* This module holds the mutable, per-extraction rendering state and registries
   shared across the C++ pretty-printers. It owns the current render context
   ([render_ctx], with save/restore snapshots), the method and name-resolution
   registries, the [std::]-namespace name configuration ([std_names]),
   eponymous-record tracking, and the wrapper/collision/global-scope tables.
   Much of the surface is intentionally mutable global state (refs and
   hashtables) that is reset between extraction units via [reset_cpp_state]. *)

(** {2 Layout combinators} *)

(** Trivial box combinators used by the pretty-printers. *)
val h : 'a -> 'a
val v : 'a -> 'b -> 'b
val hov : 'a -> 'b -> 'b

(** {2 Method registry} *)

(** Per-run and global method registries plus their accessors. *)
val method_registry : Method_registry.t option ref
val global_method_registry : Method_registry.t option ref
val set_global_method_registry : Method_registry.t -> unit
val clear_global_method_registry : unit -> unit
val get_method_registry : unit -> Method_registry.t

(** {2 Name resolution} *)

(** Name-resolution cache and its accessor. *)
val name_cache : Name_resolution.t option ref
val get_name_cache : unit -> Name_resolution.t

(** Pretty-printers for type variables and parameter lists. *)
val pp_tvar : Names.variable -> Pp.t
val pp_parameters : Names.variable list -> Pp.t
val pp_string_parameters : string list -> Pp.t

(** Look up a custom type rendering for a global reference, if any. *)
val find_type_custom_opt : Names.GlobRef.t -> (string list * string) option

(** Reserved C++ keywords that identifiers must avoid. *)
val keywords : Names.Id.Set.t

(** {2 Output modules} *)

(** Set of module paths that are valid extraction outputs. *)
val valid_output_modules : (Names.module_path, unit) Hashtbl.t
val set_valid_output_modules : Names.module_path list -> unit
val clear_valid_output_modules : unit -> unit

(** {2 Wrappers} *)

(** Global registry of wrapper names that were not merged. *)
val global_unmerged_wrappers : (string, unit) Hashtbl.t
val mark_global_unmerged : string -> unit
val is_global_unmerged : string -> bool
val clear_global_unmerged : unit -> unit

(** {2 Preamble} *)

(** Pretty-printers for includes, comments, and file preambles. *)
val pp_open : Names.module_path -> Pp.t
val pp_comment : Pp.t -> Pp.t
val pp_header_comment : Pp.t option -> Pp.t
val then_nl : Pp.t -> Pp.t
val preamble : 'a -> Pp.t option -> Names.module_path list -> 'b -> Pp.t
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
val save_render_ctx : unit -> render_ctx_snapshot
val restore_render_ctx : render_ctx_snapshot -> unit
val with_render_ctx : setup:(unit -> unit) -> (unit -> 'a) -> 'a

(** {2 Template static accessors} *)

(** Tracking for template static accessor labels and their kernel names. *)
val template_static_accessors : (Names.module_path * Names.Label.t) list ref
val template_static_accessor_kns : (Names.KerName.t, unit) Hashtbl.t
val non_accessor_labels : (Names.Label.t, unit) Hashtbl.t
val register_template_static_accessor :
  Names.module_path -> Names.Label.t -> unit

(** Map from functor-application module paths to their source module. *)
val functor_app_sources : (Names.module_path, Names.module_path) Hashtbl.t

(** {2 Eponymous records} *)

(** In-flight state used while emitting an eponymous record. *)
val eponymous_type_ref : Names.GlobRef.t option ref
val eponymous_promote_ref : Names.GlobRef.t option ref
val eponymous_deferred : Pp.t ref
val eponymous_promote_sft : bool ref
val method_candidates :
  (Names.GlobRef.t * Miniml.ml_ast * Miniml.ml_type * int) list ref
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
val default_std_names : std_names
val std_names : std_names ref
val mk_std_names : string -> std_names
val init_std_names : unit -> unit
val sn : unit -> std_names

(** Whether an ML type denotes a typeclass instance. *)
val is_typeclass_instance : 'a -> Miniml.ml_type -> bool

(** {2 Wrapper and scope tables} *)

(** Tables tracking wrapper modules, collisions, and global-scope entities. *)
val wrapper_module_table : (Names.module_path, string) Hashtbl.t
val collision_wrapper_table : (Names.module_path, unit) Hashtbl.t
val global_scope_enum_table : (Names.GlobRef.t, unit) Hashtbl.t
val global_scope_type_alias_table : (Names.GlobRef.t, unit) Hashtbl.t
val register_global_scope_type_alias : Names.GlobRef.t -> unit
val is_global_scope_type_alias : Names.GlobRef.t -> bool
val pending_wrapper_decls : (string, Pp.t) Hashtbl.t
val unmerged_wrappers : (string, unit) Hashtbl.t
val global_inductive_names : (string, Names.module_path) Hashtbl.t
val wrapper_qualify_name : Names.GlobRef.t -> string -> string

(** {2 Method registration} *)

(** Register and query methods and their any-returning status. *)
val register_method :
  Names.GlobRef.t ->
  Names.GlobRef.t -> int -> ?ind_tvar_positions:int list -> unit -> unit
val try_register_method :
  Names.GlobRef.t ->
  Names.GlobRef.t ->
  Miniml.ml_ast -> Miniml.ml_type -> Method_registry.method_candidate option
val is_registered_method : Names.GlobRef.t -> (Names.GlobRef.t * int) option
val lookup_method_ind_tvar_positions : Names.GlobRef.t -> int list
val register_method_returns_any : Names.GlobRef.t -> unit
val method_returns_any : Names.GlobRef.t -> bool

(** {2 Eponymous record registry} *)

(** Global registry and lookups for eponymous records. *)
val global_eponymous_record_registry : (Names.GlobRef.t, unit) Hashtbl.t
val eponymous_record_by_modpath :
  (Names.module_path, Names.GlobRef.t) Hashtbl.t
val register_eponymous_record : Names.GlobRef.t -> unit
val is_eponymous_record_global : Names.GlobRef.t -> bool
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
val is_suppressed_projection : Names.GlobRef.t -> bool
val filter_dfix :
  Names.GlobRef.t array ->
  'a array -> 'b array -> Names.GlobRef.t array * 'a array * 'b array
