(** The concept a module type becomes, as a value generated from its
    signature ahead of the files, which the header prints and whose
    placement is decided from it.

    What a module type's concept asks of the module [M] it constrains is
    decided here: which types are [M]'s own members (spelled
    [typename M::x]), which belong to a functor parameter, which come from a
    custom mapping.  The printer only spells those answers. *)

open Names
open Minicpp

(** A type as a concept's requirements spell it, from inside the concept. *)
type concept_type =
  | Member of {member : GlobRef.t; enum : bool; arguments : concept_type list}
      (** A type member of [M]: [typename M::x], applied to [arguments]
          through [template] when it has any. *)
  | Parameter of cpp_type
      (** A type of a parameter of the functor declaring the module type,
          which the concept is over too: [typename P::t]. *)
  | Foreign of string * concept_type list
      (** A custom mapping's template, its holes filled with the
          arguments. *)
  | Global of GlobRef.t * concept_type list  (** Any other named type, applied. *)
  | Namespaced of GlobRef.t * GlobRef.t * cpp_expr list * concept_type list
      (** A named type qualified by a namespace not inside [M], applied. *)
  | Shared_pointer of concept_type
  | Variant of variant_storage * concept_type list
  | Function of concept_type list * concept_type  (** [crane::fn<R(A...)>] *)
  | Plain of cpp_type  (** A type no requirement qualifies. *)

(** One requirement on [M]. *)
type requirement =
  | Inductive_member of {member : GlobRef.t; enum : bool; arity : int}
      (** [M] declares the inductive packet [member], of [arity] parameters. *)
  | Type_member of {member : GlobRef.t; arity : int}
      (** [M] declares the type [member], an alias template when [arity] is
          not zero. *)
  | Instance_member of {value : GlobRef.t; class_ : GlobRef.t; arguments : concept_type list}
      (** [M]'s member [value] is an instance of the type class [class_] at
          [arguments]. *)
  | Nullary_member of {value : GlobRef.t; result : concept_type}
      (** [M] has the value [value], read as data or as a nullary accessor. *)
  | Function_member of {value : GlobRef.t; parameters : concept_type list; result : concept_type}
      (** [M] has the function [value]. *)
  | Submodule of {label : Label.t; module_type : ModPath.t}
      (** [M]'s submodule [label] satisfies the concept of [module_type]. *)

(** What a module type contributes where a concept body is expected. *)
type constraint_ =
  | Named of ModPath.t  (** An existing concept, by its module type. *)
  | Requirements of signature  (** An anonymous signature's requirements. *)

and signature = {
  signature : ModPath.t;  (** The signature's own path, visible in it. *)
  parameters : ModPath.t list;  (** The functor parameters visible in it. *)
  items : item list;  (** In signature order; elements asking nothing omitted. *)
}

and item =
  | Requirement of requirement
  | Nested of ModPath.t * constraint_
      (** A nested module type, whose concept is hoisted ahead of this one. *)

(** The concept of a module type. *)
type t =
  | Alias of {base : ModPath.t; refinements : (Id.t list * cpp_type) list}
      (** Another module type's concept, conjoined with the [same_as]
          constraints of its [with Definition] refinements, innermost first.
          A [with Module] refinement constrains nothing: its module is
          declared after the concept. *)
  | Constraint of constraint_

(** [constraint_of ~params mt] is what the module type [mt] contributes
    where a concept body is expected, [params] the functor parameters
    visible in it. *)
val constraint_of : params:ModPath.t list -> Miniml.ml_module_type -> constraint_

(** [generate ~params mt] is the concept of the module type [mt], over the
    functor parameters [params] as well as [M]. *)
val generate : params:ModPath.t list -> Miniml.ml_module_type -> t

(** [names_member mp c] is whether printing [c] names, from outside the
    module [mp], one of [mp]'s members: a concept that does cannot be
    declared ahead of [mp]'s struct.  Asked of the global references the
    printer resolves by name, which are neither [M]'s members nor names
    resolved inside a signature they belong to. *)
val names_member : ModPath.t -> t -> bool
