(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression test: a top-level [main] definition (outside any module)
   must be renamed to [_main] to avoid colliding with the generated
   [int main()] wrapper.

   This mirrors the pattern used in real applications where a module
   holds the logic and a top-level [main] ties it together.
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module Greeter.

Definition greet : itree ioE unit :=
  print_endline "hello from toplevel main".

End Greeter.

Import Greeter.

Definition main : itree ioE unit := greet.

Crane Extraction "main_toplevel" Greeter main.
