(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Core module language: module types and their refinements,
    signatures, structures, module expressions, and a module binding
    ([t]: an implementation and its module type). *)

(** A module type: a path, a functor signature, an explicit signature, or
    one refined by a [with] constraint. *)
module Type = Grammar.Module_type

(** A [with] refinement fixing a type or module component by path. *)
module Refinement = Grammar.Refinement

(** One component of a module signature. *)
module Signature_item = Grammar.Signature_item

(** A module signature's components, paired with their labels. *)
module Signature = Grammar.Module_signature

(** One component of a module implementation. *)
module Structure_item = Grammar.Structure_item

(** A module expression: a path, a functor, a structure or an application. *)
module Expr = Grammar.Module_expr

(** A module structure's components, paired with their labels. *)
module Structure = Grammar.Module_structure

include Grammar.Module_binding
