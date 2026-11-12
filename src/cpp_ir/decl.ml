(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** C++ declarations ({!Grammar.Decl}), with the families only a declaration
    names. *)

include Grammar.Decl
module Namespace = Grammar.Namespace
module Variable = Grammar.Variable
module Enum = Grammar.Enum
module Constexpr = Grammar.Constexpr
