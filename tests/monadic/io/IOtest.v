(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

Import MonadNotations.

Module iotest.

  Definition test1 (s : string) : void := ghost.

  Definition test2 (s : string) : IO unit :=
    print s ;;
    Ret tt.

  Definition test3 (s : string) : IO void :=
    print_endline s ;;
    Ret ghost.

  Definition test4 : IO string :=
    print_endline "what is your name?" ;;
    s2 <- get_line ;;
    print_endline (cat "hello " s2) ;;
    Ret (cat "I read the name " (cat s2 " frome the command line!")).

  Definition test5 : IO void :=
    s <- read "file.txt" ;;
    print_endline s ;;
    Ret ghost.

End iotest.

Crane Extraction "io" iotest.
