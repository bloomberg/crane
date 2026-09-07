(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib.Strings Require Import Byte.
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** Rocq's [byte] inductive extracts to a C++ [enum] named [Byte], but the
    generated code also declares a [struct Byte] for the module wrapping it and
    then reaches into it with [Byte::x41], so the two spellings disagree. *)

Module StdlibByte.

  Definition b : byte := x41.

  Definition isA : bool := Byte.eqb b x41.

End StdlibByte.

Crane Extraction "stdlib_byte" StdlibByte.
