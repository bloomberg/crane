(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The scopes a definition written outside its struct's body is a member of
    (docs/Pipeline-Disentangling-Plan.md, Milestone 9): for each module the
    unit emits as a struct, how a definition of one of its members, written
    out of line, names that struct.  Planned from the layout and the names
    before anything is rendered ({!Cpp.plan_scopes}), installed once, and
    read by declaration: where a definition goes is a question about the
    definition, not about where a printer happens to be. *)

open Names

(** The struct a definition outside its body is a member of. *)
type scope = {
  module_ : ModPath.t;
      (** The module the struct comes from: the one whose members are its
          members.  A module flattened into a collision wrapper is a member
          of the wrapper's module. *)
  qualifier : string list;
      (** The struct's name as written from namespace scope, outermost
          first: [["Outer"; "Inner"]] is [Outer::Inner]. *)
}

val equal : scope -> scope -> bool

(** The qualifier as written, its components joined by [::]. *)
val qualifier : scope -> string

(** A unit's scopes: each module emitted as a struct, with its scope. *)
type t = (ModPath.t * scope) list

(** Make [t] the unit's scopes. *)
val install : t -> unit

(** The scope of the struct the module [mp] is emitted as, if it is emitted
    as one. *)
val of_module : ModPath.t -> scope option

(** The scope of a definition of [r] written outside every struct body:
    the one its module is emitted as, if any.  A helper lifted out of a
    declaration takes that declaration's, unless the declaration was itself
    lifted to namespace scope ({!Module_plan.is_namespace_scope_ref}), in
    which case so is the helper. *)
val of_declaration : GlobRef.t -> scope option
