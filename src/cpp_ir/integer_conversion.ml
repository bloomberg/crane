(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a value is converted to an integer type ({!Grammar.Integer_conversion}). *)

include Grammar.Integer_conversion

(** The C++ cast that spells the conversion. *)
let cast = function Exact | Wrap | To_enum -> "static_cast" | Saturate -> "std::saturate_cast"
