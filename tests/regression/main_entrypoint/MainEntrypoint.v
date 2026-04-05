(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression test: a definition named [main] returning an erased monad
   (sequential ITree mode) must generate a valid C++ entry point.

   Previously, the wrapper unconditionally emitted [_main()->run()],
   but in sequential mode the monad is erased, so [_main()] returns a
   plain type and [->run()] is invalid.
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.
Local Open Scope pstring_scope.

Module MainEntrypoint.

Definition main : itree ioE unit :=
  print_endline "hello from main".

End MainEntrypoint.

Crane Extraction "main_entrypoint" MainEntrypoint.
