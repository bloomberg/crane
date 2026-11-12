(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** C++ types ({!Grammar.Type}), with the families only a type names. *)

include Grammar.Type
module Type_variable = Grammar.Type_variable
module Erased_kind = Grammar.Erased_kind
module Variant_storage = Grammar.Variant_storage
module Reference_kind = Grammar.Reference_kind
module Type_test = Grammar.Type_test
