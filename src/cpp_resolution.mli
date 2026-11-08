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

(** The two places an enumerator is named through its enum: as a value,
    and as a case label of a [switch]. *)
type enumerator_site =
  | Enumerator_value
  | Case_label

(** The two places the type printer writes a global type's head: a type
    named by its global ([Tglob]), and an inductive written through the
    struct it is declared in ([Tnamespace]). *)
type head_form =
  | Glob_head
  | Inductive_head

(** What is named, each as the naming function the printer would ask. *)
type key =
  | Module of ModPath.t  (** The module, as its struct is named. *)
  | Module_declared of ModPath.t
      (** The name the module's struct, or the alias standing for it, is
          declared under. *)
  | Global of Common.kind * GlobRef.t
      (** The global: an inline custom mapping's text, or its name. *)
  | Unmapped of Common.kind * GlobRef.t
      (** The global's name, whatever an inline custom mapping says. *)
  | Inductive_value of GlobRef.t
      (** The inductive type, written as a value: the struct a constructor's
          value is built through. *)
  | Short of Common.kind * GlobRef.t  (** Its name in its own scope, unqualified. *)
  | Class_concept of GlobRef.t  (** The concept of the type class. *)
  | Modtype_concept of ModPath.t  (** The concept of the module type, named. *)
  | Modtype_concept_declared of ModPath.t
      (** The name the concept of the module type is declared under. *)
  | Definition of definition * GlobRef.t
      (** The name the type is defined under, declared as the definition
          says. *)
  | Custom_text of GlobRef.t
      (** The text of the global's custom mapping, foreign: what a type or
          a value it maps is instantiated from. *)
  | Inline_custom of GlobRef.t
      (** Whether the global is written as the text of an inline custom
          mapping, and the text: asked for every global a declaration
          names, so a global not asked for is a planning miss, never a
          global written otherwise.  An {!Inline} answer, not a name. *)
  | Inductive_scope of GlobRef.t
      (** The struct a member of the inductive type is named through. *)
  | Type_head of head_form * GlobRef.t
      (** The global written as a type's head, in the form given: a
          {!head}, not a name. *)
  | Value_reference of GlobRef.t
      (** The constant or constructor written as a value: a
          {!reference}, not a name. *)
  | Value_access of GlobRef.t
      (** Whether a value naming the global reads a variable or calls the
          accessor standing for it: an {!access}, asked for every global a
          declaration names. *)
  | Built_struct of GlobRef.t
      (** The struct a value of the type is built through, named. *)
  | Enumerator_qualifier of enumerator_site * GlobRef.t
      (** The enum an enumerator of the inductive is named through, at the
          site given, with the [::] a nested struct of the same name asks
          for in front of it. *)
  | Read_by_a_function of GlobRef.t
      (** Whether a function body of the program reads the variable, so
          that every unit including its header has to initialise it: a
          {!Holds} answer, asked for every global. *)
  | Held_back_concept of GlobRef.t
      (** Whether the concept of the type class is held back here: declared
          after the struct being written, so that neither a constraint nor
          an assertion names it inside it.  A {!Holds} answer, asked for
          every type class. *)

val pp_key : key -> Pp.t

(** A type's head as written: the qualifiers in front of it, the name
    itself, whether it asks for [typename] in front, and whether template
    arguments following it ask for the [template] disambiguator. *)
type head = {
  outer : Cpp_name.scope list;
  head : Cpp_name.t;
  typename : bool;
  templated : bool;
}

(** A constant or constructor as an expression names it. *)
type reference =
  | Named_value of {name : Cpp_name.t; type_arguments : bool}
      (** By [name], qualified as it is to be written; followed by the
          template arguments of the use if [type_arguments]: a function of
          an eponymous record of no parameters writes none. *)
  | Record_member of {record : GlobRef.t; type_params : int}
      (** As a static member of the eponymous record [record], a class
          template of [type_params] parameters, through the record. *)

(** How a value naming a global reads it. *)
type access =
  | Variable  (** As the variable it is. *)
  | Accessor  (** By calling the accessor (a Meyers singleton) standing for it. *)
  | Either_form
      (** Through a bound module parameter, whose argument may define it
          either way: whichever it does. *)

(** What a key resolves to: a {!Type_head} a head, an {!Inline_custom}
    the inline text or none, a {!Value_reference} a reference, a
    {!Value_access} an access, a {!Read_by_a_function} or a
    {!Held_back_concept} whether it holds, anything else a name. *)
type value =
  | Name of Cpp_name.t
  | Head of head
  | Inline of string option
  | Reference of reference
  | Access of access
  | Holds of bool

val pp_reference : reference -> Pp.t
val pp_access : access -> Pp.t

(** The name a key other than {!Type_head} resolves to. *)
val name_of : key -> value -> Cpp_name.t

(** A declaration's names, by frame and key. *)
type table

(** The names of a declaration not resolved yet. *)
val unresolved : table

(** [resolve value requests] is the table resolving each of [requests] as
    [value] resolves it at its frame. *)
val resolve : (frame -> key -> value) -> (frame * key) list -> table

type 'a lookup =
  | Found of 'a
  | Unresolved  (** The table was never resolved. *)
  | Not_requested  (** It was, but this was not asked for. *)

(** The name [key], not a {!Type_head}, resolved to at [frame]. *)
val find : table -> frame -> key -> Cpp_name.t lookup

(** The head the global resolved to at [frame], in the form given. *)
val find_head : table -> frame -> head_form -> GlobRef.t -> head lookup

(** The inline custom text of the global at [frame], if it has one
    ({!Inline_custom}). *)
val find_inline : table -> frame -> GlobRef.t -> string option lookup

(** How the constant or constructor is written as a value at [frame]
    ({!Value_reference}). *)
val find_reference : table -> frame -> GlobRef.t -> reference lookup

(** How a value naming the global reads it at [frame] ({!Value_access}). *)
val find_access : table -> frame -> GlobRef.t -> access lookup

(** Whether [key], a {!Read_by_a_function} or a {!Held_back_concept},
    holds at [frame]. *)
val find_holds : table -> frame -> key -> bool lookup
