(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The plan facts an extraction accumulates over its units: what a unit is
    planned and rendered with of its own plan and of the plans of the units
    extracted before it.  A separate extraction renders one unit per file,
    and a later unit reads what an earlier one decided -- how an earlier
    file's inductive is promoted, which of its constants are accessors,
    which wrapper struct holds it -- so the driver threads this value from
    unit to unit ([Extract_env.print_per_library]): a unit starts from what
    the earlier ones leave ({!for_next_unit}), and its planning extends it
    one decision at a time, each extension bound ({!bind}) for the rest of
    the unit. *)

open Names

type t = {
  modules : Module_plan.layout;
      (** The layout: where each declaration lives and what it is called
          ({!Module_plan.extend}). *)
  pointer_fields : Loopify_analysis.pointer_fields;
      (** The fields each constructor struct stores behind the pointer. *)
  unmerged_wrappers : ModPath.t CString.Map.t;
      (** The wrapper structs that hold declarations, by name, each with
          the module it wraps. *)
  promoted_inductives : Ref.User.Set.t;
      (** The inductives promoted to their eponymous module's struct. *)
  accessors : Cpp_state.accessors;
      (** The constants emitted as accessor functions. *)
  nested_structs : Cpp_state.nested_struct_owner list CString.Map.t;
      (** The structs written inside another struct, by name. *)
  instance_promoted_types : (Id.t * Core.Type.t) list GlobRef.Map.t;
      (** The concrete types each instance gives its class's promoted
          variables. *)
}

(** What the first unit of an extraction starts from: [accessors], those
    a pre-scan of the whole program found, and nothing else. *)
val start : accessors:Cpp_state.accessors -> t

(** [context t u] is the unit's context [u] holding the facts of [t] its
    readers read off it: the layout. *)
val context : t -> Unit_context.t -> Unit_context.t

(** [bind t f] is [f ()] with each other fact of [t] the one its readers
    answer from ({!Loopify_analysis.with_pointer_fields},
    {!Cpp_state.with_unmerged_wrappers}, {!Table.with_promoted_inductives},
    {!Cpp_state.with_accessors}, {!Cpp_state.with_nested_struct_names},
    {!Table.with_instance_promoted_types}). *)
val bind : t -> (unit -> 'a) -> 'a

(** What the next unit of the extraction starts from, once a unit planned
    [t]: [t] without the facts that belong to one unit, the per-unit
    layout ({!Module_plan.for_next_unit}).  The callable plans are the
    unit's own ({!Unit_context.t.callables}): a callee another unit defines
    is planned as foreign ({!Callable_abi.with_foreign}). *)
val for_next_unit : t -> t
