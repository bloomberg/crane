(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The context of one unit's extraction.  See [unit_context.mli]. *)

type t = {
  config : Table.unit_config;
  callables : Callable_abi.decided;
  modules : Module_plan.layout;
  pointer_fields : Pointer_fields.t;
  unmerged_wrappers : Names.ModPath.t CString.Map.t;
  accessors : Struct_plan.accessors;
  nested_structs : Struct_plan.nested_structs;
  promoted_inductives : Ref.User.Set.t;
  instance_promoted_types : (Names.Id.t * Core.Type.t) list Names.GlobRef.Map.t;
  scopes : Scope_plan.bound;
}

let make ~config =
  { config;
    callables = Callable_abi.undecided;
    modules = Module_plan.no_layout;
    pointer_fields = Pointer_fields.none;
    unmerged_wrappers = CString.Map.empty;
    accessors = Struct_plan.no_accessors;
    nested_structs = CString.Map.empty;
    promoted_inductives = Ref.User.Set.empty;
    instance_promoted_types = Names.GlobRef.Map.empty;
    scopes = Scope_plan.none }
let detached = make ~config:{Table.concurrent = false}
let non_atomic_rc u = Table.non_atomic_rc_for u.config
let count_rc u = Table.count_rc_for u.config
let is_promoted_inductive u r = Ref.User.Set.mem r u.promoted_inductives

let instance_promoted_types_of u r =
  match Names.GlobRef.Map.find_opt r u.instance_promoted_types with Some bindings -> bindings | None -> []
