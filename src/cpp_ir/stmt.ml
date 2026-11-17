(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** C++ statements ({!Grammar.Stmt}), with the families only a statement
    names. *)

include Grammar.Stmt
module Binding = Grammar.Binding
module Match = Grammar.Match
module Custom_match = Grammar.Custom_match
module Foreign_block = Grammar.Foreign_block
module Precondition = Grammar.Precondition
