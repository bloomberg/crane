(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The Core module language: module types and their refinements,
    signatures, structures, module expressions, and a module binding
    ([t]: {!Grammar.Module_binding}). *)

module Type = Grammar.Module_type
module Refinement = Grammar.Refinement
module Signature_item = Grammar.Signature_item
module Signature = Grammar.Module_signature
module Structure_item = Grammar.Structure_item
module Expr = Grammar.Module_expr
module Structure = Grammar.Module_structure
include Grammar.Module_binding
