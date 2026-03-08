(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Pre-computed C++ name resolution cache.

   This module moves name resolution logic out of cpp.ml's pretty-printer
   into a pre-computation phase that runs during translation.  The cache
   maps GlobRef.t values to resolved C++ names, eliminating the need for
   complex name resolution at render time.

   The cache is populated once per extraction pass by [create], which
   scans the full ml_structure and resolves every inductive type name
   and global function name according to the same rules that cpp.ml
   previously applied at render time (wrapper qualification, eponymous
   record merging, collision detection, etc.).

   Usage:
     let nrc = Name_resolution.create analysis wrapper_module_table ... in
     match Name_resolution.resolve_type nrc r with
     | Some name -> (* use pre-resolved name *)
     | None -> (* fall back to current logic *)
*)

open Names
open Minicpp

(** Opaque cache type. *)
type t

(** Pre-resolved name for a type reference. *)
type resolved_type_name = {
  rtn_display : string;       (** The full display string (e.g., "List", "Nat::nat", "CHT") *)
  rtn_is_eponymous : bool;    (** True if this is an eponymous record merged into module *)
  rtn_is_record : bool;       (** True if this is a record (not standard inductive) *)
  rtn_is_enum : bool;         (** True if this is an enum class *)
  rtn_is_local : bool;        (** True if defined in the current module scope *)
  rtn_is_merged : bool;       (** True if the Dnspace wrapper was merged *)
  rtn_is_global_scope_enum : bool;  (** True if this enum is at global scope *)
}

(** Pre-resolved name for a term (function/constant) reference. *)
type resolved_term_name = {
  rtm_display : string;       (** The display string (e.g., "add", "Nat::div") *)
  rtm_wrapper_qualified : bool;  (** True if name was wrapper-qualified *)
}

(** Create a name resolution cache from analysis results.
    Should be called once per extraction pass, after Structure_analysis.analyze
    and after wrapper_module_table / collision_wrapper_table are populated. *)
val create :
  structure_analysis:Structure_analysis.t ->
  wrapper_modules:(ModPath.t, string) Hashtbl.t ->
  collision_wrappers:(ModPath.t, unit) Hashtbl.t ->
  global_scope_enums:(GlobRef.t, unit) Hashtbl.t ->
  eponymous_records:(GlobRef.t, unit) Hashtbl.t ->
  unmerged:(string, unit) Hashtbl.t ->
  Miniml.ml_structure ->
  t

(** Look up a pre-resolved type name. Returns None if not cached. *)
val resolve_type : t -> GlobRef.t -> resolved_type_name option

(** Look up a pre-resolved term name. Returns None if not cached. *)
val resolve_term : t -> GlobRef.t -> resolved_term_name option

(** Register a type name resolution. Used for late entries (e.g., local inductives). *)
val register_type : t -> GlobRef.t -> resolved_type_name -> unit

(** Register a term name resolution. *)
val register_term : t -> GlobRef.t -> resolved_term_name -> unit

(** Check if a type is an eponymous record (pre-computed). *)
val is_eponymous : t -> GlobRef.t -> bool

(** Check if a type is an enum at global scope (pre-computed). *)
val is_global_scope_enum : t -> GlobRef.t -> bool

(** Get the inductive classification for a type. *)
val get_ind_kind : t -> GlobRef.t -> cpp_ind_kind option

(** Register an inductive classification. *)
val register_ind_kind : t -> GlobRef.t -> cpp_ind_kind -> unit
