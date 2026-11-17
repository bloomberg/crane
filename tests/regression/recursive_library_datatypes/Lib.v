(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Crane Recursive Extraction Library] writes a [Datatypes.h]
    that does not compile.  It declares the standard library's [sum] and
    [list] as [struct Sum] and [List], but their converting constructors
    and other uses in the same header spell them [sum<...>] and
    [list<...>]: "no template named 'sum'", "no template named 'list'".
    The non-recursive [Crane Extraction Library] leaves [Datatypes.h] to the
    user. *)

From Crane Require Import Extraction.
From CraneTestsRegression Require recursive_library_datatypes.Src.

Crane Recursive Extraction Library Src.
