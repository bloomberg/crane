(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The plan facts an extraction accumulates over its units.  See
    [accumulated_plan.mli]. *)

open Names

type t = {
  modules : Module_plan.layout;
  pointer_fields : Pointer_fields.t;
  unmerged_wrappers : ModPath.t CString.Map.t;
  promoted_inductives : Ref.User.Set.t;
  accessors : Cpp_state.accessors;
  nested_structs : Cpp_state.nested_struct_owner list CString.Map.t;
  instance_promoted_types : (Id.t * Core.Type.t) list GlobRef.Map.t;
}

let start ~accessors =
  { modules = Module_plan.no_layout;
    pointer_fields = Pointer_fields.none;
    unmerged_wrappers = CString.Map.empty;
    promoted_inductives = Ref.User.Set.empty;
    accessors;
    nested_structs = CString.Map.empty;
    instance_promoted_types = GlobRef.Map.empty }

let context t (u : Unit_context.t) =
  { u with
    modules = t.modules;
    pointer_fields = t.pointer_fields;
    unmerged_wrappers = t.unmerged_wrappers;
    accessors = t.accessors;
    nested_structs = t.nested_structs }

let bind t f =
  Table.with_promoted_inductives t.promoted_inductives @@ fun () ->
  Table.with_instance_promoted_types t.instance_promoted_types f

let for_next_unit t = {t with modules = Module_plan.for_next_unit t.modules}
