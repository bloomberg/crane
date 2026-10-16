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

(** A unit's scopes: each module emitted as a struct, with its scope; the
    modules written inside a struct's body -- a struct's or a functor's,
    which the header writes as a class template -- rather than outside every
    struct; and the modules whose members the header writes inside a class
    template. *)
type t = {
  scopes : (ModPath.t * scope) list;
  nested : ModPath.t list;
  templated : ModPath.t list;
}

val empty : t

val equal_plans : t -> t -> bool

(** Make [t] the unit's scopes. *)
val install : t -> unit

(** The scope of the struct the module [mp] is emitted as, if it is emitted
    as one. *)
val of_module : ModPath.t -> scope option

(** Whether the module [mp] is written inside a struct's body.  The same in
    both files, though only the header writes the struct. *)
val nested : ModPath.t -> bool

(** Whether the header writes the members of the module [mp] inside a class
    template -- a functor's body, a module promoted to its eponymous
    inductive's template, or a module nested in either -- and so defines
    them there, where the implementation writes none of them.  A question
    about the module, answered the same for both files. *)
val templated : ModPath.t -> bool

(** The scope of a definition of [r] written outside every struct body:
    the one its module is emitted as, if any.  A helper lifted out of a
    declaration takes that declaration's, unless the declaration was itself
    lifted to namespace scope ({!Module_plan.is_namespace_scope_ref}), in
    which case so is the helper. *)
val of_declaration : GlobRef.t -> scope option
