(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a module's own declarations say about how its body is written
    (docs/Pipeline-Disentangling-Plan.md, Milestone 9): a function of the
    module and of the structure declaring it, the same in both files, and
    so a fact to plan rather than one a render discovers on its way in. *)

open Names

type t = {
  eponymous_type : GlobRef.t option;
      (** The inductive the module is named after, case aside, that is
          neither a record nor a class: functions taking it become its
          methods. *)
  eponymous_record : (GlobRef.t * Miniml.record_field list * Miniml.ml_ind_packet) option;
      (** The record the module is named after, merged into its struct. *)
  method_candidates : Method_registry.method_candidate list;
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

(** [of_module mp ~name sel ~enclosing] is the frame of the module [mp],
    printed [name], of elements [sel], declared among [enclosing]. *)
val of_module :
  ModPath.t ->
  name:string ->
  (Label.t * Miniml.ml_structure_elem) list ->
  enclosing:(Label.t * Miniml.ml_structure_elem) list ->
  t
