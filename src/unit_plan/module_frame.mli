(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a module's own declarations say about how its body is written: a
    function of the module and of the structure declaring it, the same in
    both files, and so a fact planned by the walk ahead of the files rather
    than one a render discovers on its way in.  The printer reads the
    planned frame ({!planned}) when it writes the module's struct. *)

open Names

(** The frame of one module. *)
type t = Cpp_state.module_frame = {
  eponymous_type : GlobRef.t option;
      (** The inductive the module is named after, case aside, that is
          neither a record nor a class: functions taking it become its
          methods. *)
  eponymous_record : (GlobRef.t * Core.Record.Field.t list * Core.Inductive.Packet.t) option;
      (** The record the module is named after, merged into its struct. *)
  method_candidates : Core_plan.Method_registry.method_candidate list;
      (** The functions of the module and of the structure declaring it
          that become methods of the eponymous inductive or record, newest
          first; none for a custom type or an enum, which hold none. *)
  concept_collision : bool;
      (** Whether a class the module declares has a concept named as the
          module is, in which case the header writes no struct for it. *)
  promoted : Id.t list option;
      (** The template parameters of the eponymous inductive, where the
          module's struct is that inductive promoted. *)
}

(** [of_module u mp ~name sel ~enclosing] is the frame of the module [mp],
    printed [name], of elements [sel], declared among [enclosing], in the
    unit [u]. *)
val of_module :
  Context.t ->
  ModPath.t ->
  name:string ->
  (Label.t * Core.Module.Structure_item.t) list ->
  enclosing:(Label.t * Core.Module.Structure_item.t) list ->
  t

(** Whether a class [sel] declares has a concept named as the module [mp]
    is, by the names both are planned under in [layout]. *)
val concept_collision : Core_plan.Module_plan.layout -> ModPath.t -> (Label.t * Core.Module.Structure_item.t) list -> bool

(** Whether two frames say the same of a module: the same eponymous
    inductive and record, the same candidates at the same receiver
    positions, the same collision and promotion. *)
val equal : t -> t -> bool

(** The frame [plans] has for a module, which the walk ahead of the files
    works out ({!Cpp.walk_as_rendered}); an anomaly where none was
    planned. *)
val planned : Cpp_state.plans -> ModPath.t -> t

(** The modules whose frames the body of the module [mp] is written in,
    innermost first, as [scopes] plans them ({!Core_plan.Scope_plan.frames}). *)
val frames_around : Core_plan.Scope_plan.bound -> ModPath.t -> ModPath.t list

(** The inductives not promoted in the body of the module [mp]: the
    eponymous inductive of each frame around it that does not promote it,
    whatever the unit's plan promotes, the frames as [plans] has them;
    [scopes] is the unit's scope plan. *)
val demoted_around : Cpp_state.plans -> Core_plan.Scope_plan.bound -> ModPath.t -> GlobRef.t list
