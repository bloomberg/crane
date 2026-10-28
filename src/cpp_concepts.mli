(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The C++ concept a module type becomes ({!Modtype_concept.t}), as text:
    its declaration, the concepts of the module types nested in it, and the
    name every reference to it spells. *)

open Names

(** [pp_modtype_concept ~names ~params path c] is the declaration of the
    concept of the module type at [path], generated as [c], over [M] and the
    parameters [params] of a functor declaring it, with the concepts its
    nested module types are hoisted into ahead of it, naming what [names]
    names ({!names_requested}). *)
val pp_modtype_concept :
  names:Cpp_resolution.table -> params:ModPath.t list -> ModPath.t -> Modtype_concept.t -> Pp.t

(** The assertion [a], as written where the tree puts it. *)
val pp_assertion : Cpp_ast.assertion -> Pp.t

(** What a declaration not yet printed names, at the frames inside it,
    beyond the references the tree holds itself: what
    {!Cpp_ast.resolve_tree} resolves into its table.  Of a module type's
    concept, everything but the types the type printer writes. *)
val names_requested : Cpp_ast.declaration -> (Cpp_resolution.frame * Cpp_resolution.key) list
