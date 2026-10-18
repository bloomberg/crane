(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ concept a module type becomes ({!Modtype_concept.t}), as text:
    its declaration, the concepts of the module types nested in it, and the
    name every reference to it spells. *)

open Names

(** The functor whose body declares module types at [mp], by its label, with
    its parameters, as {!Cpp_state.functor_concept_scopes} records it. *)
val functor_concept_scope : ModPath.t -> (Label.t * ModPath.t list) option

(** The arguments, after the constrained module, of the concept of the module
    type [kn]: the parameters of the functor declaring it, if one does. *)
val concept_extra_args : ModPath.t -> ModPath.t list

(** The C++ identifier of the concept the module type at [mp] becomes, at
    its declaration and at every reference. *)
val modtype_concept_name : ModPath.t -> string

(** The concept of the module type [kn], as a reference spells it. *)
val pp_concept_ref : ModPath.t -> Pp.t

(** [pp_modtype_concept ?params name c] is the declaration of the concept
    [name] of a module type generated as [c], over [M] and the parameters
    [params] of a functor declaring it, with the concepts its nested module
    types are hoisted into ahead of it. *)
val pp_modtype_concept : ?params:ModPath.t list -> Pp.t -> Modtype_concept.t -> Pp.t

(** The assertion [a], as written where the tree puts it. *)
val pp_assertion : Cpp_ast.assertion -> Pp.t
