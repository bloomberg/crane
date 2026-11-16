(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The plan facts an extraction accumulates over its units.  See
    [accumulated_plan.mli]. *)

open Names

type t = {
  modules : Module_plan.layout;
  pointer_fields : Loopify_analysis.pointer_fields;
  unmerged_wrappers : ModPath.t CString.Map.t;
  promoted_inductives : Ref.User.Set.t;
  accessors : Cpp_state.accessors;
  nested_structs : Cpp_state.nested_struct_owner list CString.Map.t;
  instance_promoted_types : (Id.t * Core.Type.t) list GlobRef.Map.t;
}

let start ~accessors =
  { modules = Module_plan.no_layout;
    pointer_fields = Loopify_analysis.no_pointer_fields;
    unmerged_wrappers = CString.Map.empty;
    promoted_inductives = Ref.User.Set.empty;
    accessors;
    nested_structs = CString.Map.empty;
    instance_promoted_types = GlobRef.Map.empty }

let context t (u : Unit_context.t) = {u with modules = t.modules}

let bind t f =
  Loopify_analysis.with_pointer_fields t.pointer_fields @@ fun () ->
  Cpp_state.with_unmerged_wrappers t.unmerged_wrappers @@ fun () ->
  Table.with_promoted_inductives t.promoted_inductives @@ fun () ->
  Cpp_state.with_accessors t.accessors @@ fun () ->
  Cpp_state.with_nested_struct_names t.nested_structs @@ fun () ->
  Table.with_instance_promoted_types t.instance_promoted_types f

let for_next_unit t = {t with modules = Module_plan.for_next_unit t.modules}
