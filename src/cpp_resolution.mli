(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a declaration names, resolved before it is printed
    (docs/Pipeline-Disentangling-Plan.md, section 8.5 and Milestone 9: the
    seed of [ResolveCppNames]).

    A name is resolved where it is written, and inside one declaration that
    is not always where the declaration is: printing a module type's concept
    enters each anonymous signature in it, whose own members are named there
    unqualified.  So a name is resolved at a frame, the scopes printing has
    entered inside the declaration's own, and a declaration's names are a
    table keyed by frame and by what is named. *)

open Names

(** A scope printing a declaration enters inside the one it is written in. *)
type entered =
  | Signature of {signature : ModPath.t; parameters : ModPath.t list}
      (** An anonymous signature's requirements, its own path and the functor
          parameters visible in it visible. *)
  | Inductive_struct of GlobRef.t
      (** The scope the struct of the inductive opens, between its module and
          its members: the constructors' structs declared in it hide what the
          module declares under their names. *)
  | In_struct  (** A struct's body. *)
  | In_template  (** A class template's body. *)
  | Function of {owner : GlobRef.t; defines : bool}
      (** A function of the declaration [owner] -- defined, if [defines] --
          which outside every struct body is defined out of line, as a member
          of the struct its plan's scope names. *)

(** The scopes entered, innermost first; [[]] is where the declaration is
    written. *)
type frame = entered list

(** How a type a member alias stands in for is declared, which is the name
    it is declared under. *)
type definition =
  | Enum_definition  (** A scoped enum. *)
  | Struct_definition  (** A struct. *)
  | Alias_definition  (** A [using] declaration. *)

(** What is named, each as the naming function the printer would ask. *)
type key =
  | Module of ModPath.t  (** The module, as its struct is named. *)
  | Global of Common.kind * GlobRef.t
      (** The global: an inline custom mapping's text, or its name. *)
  | Unmapped of Common.kind * GlobRef.t
      (** The global's name, whatever an inline custom mapping says. *)
  | Short of Common.kind * GlobRef.t  (** Its name in its own scope, unqualified. *)
  | Class_concept of GlobRef.t  (** The concept of the type class. *)
  | Modtype_concept of ModPath.t  (** The concept of the module type, named. *)
  | Modtype_concept_declared of ModPath.t
      (** The name the concept of the module type is declared under. *)
  | Definition of definition * GlobRef.t
      (** The name the type is defined under, declared as the definition
          says. *)

val pp_key : key -> Pp.t

(** A declaration's names, by frame and key. *)
type table

(** The names of a declaration not resolved yet. *)
val unresolved : table

(** [resolve name requests] is the table naming each of [requests] as
    [name] names it at its frame. *)
val resolve : (frame -> key -> Cpp_name.t) -> (frame * key) list -> table

type lookup =
  | Found of Cpp_name.t
  | Unresolved  (** The table was never resolved. *)
  | Not_requested  (** It was, but this was not asked for. *)

val find : table -> frame -> key -> lookup
