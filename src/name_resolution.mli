(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** {1 Name Resolution}

    A per-extraction cache of how each inductive type is rendered.

    {!create} scans the [ml_structure] once, after
    {!Structure_analysis.analyze} and before rendering, and records for every
    inductive declared at top level or in a module structure its
    classification ({!Cpp_ir.Inductive.Kind}: sum, enum, record,
    eponymous record or type class).  The printer reads the classification
    through {!Cpp_names}, falling back to the live tables for an inductive
    the scan did not see.  Nothing here qualifies or renames a name.

    {2 Usage}

    {[
      let nrc = Name_resolution.create s in
      match Name_resolution.get_ind_kind nrc r with
      | Some kind -> (* the scan classified [r] *)
      | None -> (* not scanned: classify from the tables *)
    ]}

    {b Side-effect caveat.} Unlike a naive render-time resolver, {!create} must
    avoid [Common.pp_global] / [Common.pp_global_name], because those mutate
    [Common]'s renaming tables; touching them at cache-creation time would emit
    premature renaming entries and change the output. This is why no name is
    pre-computed. *)

open Names

(** The cache: an inductive kind per scanned inductive. *)
type t

(** Create the cache for a structure. Called once per extraction pass, after
    {!Structure_analysis.analyze}.  Inductives inside functor bodies are not
    scanned.
    @return a freshly built name resolution cache *)
val create : Miniml.ml_structure -> t

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
val get_ind_kind : t -> GlobRef.t -> Cpp_ir.Inductive.Kind.t option
