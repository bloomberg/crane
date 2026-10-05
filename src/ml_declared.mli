(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** MiniML read through declared meanings ({!Mapping_semantics}): what the
    passes that compute or rewrite with them share. *)

(** Whether [e] is built from declared operations, constructors, literals and
    variables only, and so evaluates to a value and does nothing else, at any
    point: neither throws, nor diverges, nor has an effect.  A mapping without
    a declaration is not one, whatever its text. *)
val pure : Miniml.ml_ast -> bool

(** Every definition's body in the structure, by reference -- in modules,
    not functors -- for calls to follow. *)
val definitions : Miniml.ml_structure -> Miniml.ml_ast Table.Refmap'.t

(** [map_decls f s] applies [f] to every declaration of [s], in modules and
    functors alike. *)
val map_decls : (Miniml.ml_decl -> Miniml.ml_decl) -> Miniml.ml_structure -> Miniml.ml_structure
