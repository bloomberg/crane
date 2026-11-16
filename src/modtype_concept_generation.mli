(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Generating the concept a module type becomes ({!Cpp_ast.Modtype_concept.t}) from
    the Core module type: each type is converted through translation's type
    conversion and lowered to CppIR.  It runs where the module type is
    generated, ahead of the files. *)

open Names

(** [constraint_of ~params mt] is what the module type [mt] contributes
    where a concept body is expected, [params] the functor parameters
    visible in it. *)
val constraint_of : Translation_state.t -> params:ModPath.t list -> Core.Module.Type.t -> Cpp_ast.Modtype_concept.constraint_

(** [generate ~params mt] is the concept of the module type [mt], over the
    functor parameters [params] as well as [M]. *)
val generate : Translation_state.t -> params:ModPath.t list -> Core.Module.Type.t -> Cpp_ast.Modtype_concept.t
