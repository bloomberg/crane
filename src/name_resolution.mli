(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** {1 Name Resolution}

    A per-extraction cache of how each inductive type is rendered.

    {!create} scans the [ml_structure] once, after
    {!Structure_analysis.analyze} and before rendering, and records for every
    inductive declared at top level or in a module structure its
    classification ({!Minicpp.cpp_ind_kind}: standard, enum, record,
    eponymous record or type class) and its raw type name.  The printer reads
    the classification through {!Cpp_names}, falling back to the live tables
    for an inductive the scan did not see.  Nothing here qualifies or renames
    a name: [rtn_display] is the Rocq type name as declared.

    {2 Usage}

    {[
      let nrc = Name_resolution.create ~structure_analysis:analysis s in
      match Name_resolution.get_ind_kind nrc r with
      | Some kind -> (* the scan classified [r] *)
      | None -> (* not scanned: classify from the tables *)
    ]}

    {b Side-effect caveat.} Unlike a naive render-time resolver, {!create} must
    avoid [Common.pp_global] / [Common.pp_global_name], because those mutate
    [Common]'s renaming tables; touching them at cache-creation time would emit
    premature renaming entries and change the output. This is why term names are
    deliberately {i not} pre-computed (see {!resolve_term}). *)

open Names
open Minicpp

(** The cache: a type name and an inductive kind per scanned inductive. *)
type t

(** Pre-resolved name for a type reference. *)
type resolved_type_name = {
  rtn_display : string;
      (** The Rocq type name as declared, unqualified and not renamed *)
  rtn_is_eponymous : bool;
      (** True if this is an eponymous record merged into module *)
  rtn_is_record : bool;
      (** True if this is a record (not standard inductive) *)
  rtn_is_enum : bool;  (** True if this is an enum class *)
  rtn_is_local : bool;
      (** True if defined in the current module scope; {!create} records
          [false] for every inductive *)
  rtn_is_global_scope_enum : bool;  (** True if this enum is at global scope *)
}

(** Pre-resolved name for a term (function/constant) reference. *)
type resolved_term_name = {
  rtm_display : string;  (** The display string (e.g., "add", "Nat::div") *)
  rtm_wrapper_qualified : bool;  (** True if name was wrapper-qualified *)
}

(** Create the cache for a structure. Called once per extraction pass, after
    {!Structure_analysis.analyze}.  Inductives inside functor bodies are not
    scanned.
    @param structure_analysis the result of {!Structure_analysis.analyze};
      currently unused
    @return a freshly built name resolution cache *)
val create :
  structure_analysis:Structure_analysis.t ->
  Miniml.ml_structure ->
  t

(** Look up a pre-resolved type name. Returns None if not cached.
    @param t the name resolution cache
    @param r the global reference to look up
    @return [Some info] if the type has been pre-classified, [None] otherwise *)
val resolve_type : t -> GlobRef.t -> resolved_type_name option

(** Look up a pre-resolved term name.
    @param t the name resolution cache
    @param r the global reference to look up
    @return always [None]: term names are deliberately not pre-computed (to
            avoid renaming side effects at cache-creation time), so this is a
            stub kept only to mirror {!resolve_type}. *)
val resolve_term : t -> GlobRef.t -> resolved_term_name option

(** Register a type name resolution. Used for late entries (e.g., local
    inductives).
    @param t the cache to update
    @param r the global reference to register
    @param name the resolved name information to store *)
val register_type : t -> GlobRef.t -> resolved_type_name -> unit

(** Register a term name resolution. Currently a no-op: term names are not
    cached (see {!resolve_term}); this is a stub kept to mirror
    {!register_type}.
    @param t the cache (left unchanged)
    @param r the global reference (ignored)
    @param name the resolved name information (ignored) *)
val register_term : t -> GlobRef.t -> resolved_term_name -> unit

(** Check if a type is an eponymous record.  Reads
    {!Module_plan.is_eponymous_record}, not the cache.
    @param t the name resolution cache (ignored)
    @param r the inductive reference to test
    @return [true] if [r] is an eponymous record flattened into its parent namespace *)
val is_eponymous : t -> GlobRef.t -> bool

(** Check if a type is an enum at global scope.  Reads
    {!Module_plan.is_global_scope_enum}, not the cache.
    @param t the name resolution cache (ignored)
    @param r the inductive reference to test
    @return [true] if [r] is an enum class emitted at global scope *)
val is_global_scope_enum : t -> GlobRef.t -> bool

(** Get the inductive classification for a type.
    @param t the name resolution cache
    @param r the inductive reference to look up
    @return [Some kind] if the classification has been registered, [None] otherwise *)
val get_ind_kind : t -> GlobRef.t -> cpp_ind_kind option

(** Register an inductive classification.
    @param t the cache to update
    @param r the inductive reference to classify
    @param kind the C++ rendering kind to associate with [r] *)
val register_ind_kind : t -> GlobRef.t -> cpp_ind_kind -> unit
