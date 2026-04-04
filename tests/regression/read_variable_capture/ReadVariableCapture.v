(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Bug: [read]'s inline custom uses [[]()]  (no-capture lambda) instead of
   [[&]()].  When called with a variable argument (not a literal), the
   generated C++ lambda references an outer variable without capturing it,
   producing a compilation error.

   Contrast with [write_file], which correctly uses [[&]()].
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module ReadVariableCapture.

  (** Works: literal argument — no capture needed *)
  Definition read_literal : itree ioE string :=
    content <- read "file.txt" ;;
    Ret content.

  (** Bug: variable argument — [path] not captured by [[]() { ... path ... }()] *)
  Definition read_variable (path : string) : itree ioE string :=
    content <- read path ;;
    Ret content.

  (** Bug: same issue with [file_exists] which is [std::filesystem::exists(...)],
      but that's a plain expression, not a lambda, so it works.
      This test is for [read] specifically. *)
  Definition read_and_check (path : string) : itree ioE string :=
    ok <- file_exists path ;;
    if ok then
      read path
    else
      Ret "".

End ReadVariableCapture.

Crane Extraction "read_variable_capture" ReadVariableCapture.
