(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

Module iotest.

  Definition test1 (s : string) : unit := tt.

  Definition test2 (s : string) : itree iIO unit :=
    print s ;;
    Ret tt.

  Definition test3 (s : string) : itree iIO unit :=
    print_endline s ;;
    Ret tt.

  Definition test4 : itree iIO string :=
    print_endline "what is your name?" ;;
    s2 <- get_line ;;
    print_endline (cat "hello " s2) ;;
    Ret (cat "I read the name " (cat s2 " from the command line!")).

  Definition test5 : itree iIO unit :=
    s <- read "file.txt" ;;
    print_endline s ;;
    Ret tt.

End iotest.

Crane Extraction "io" iotest.
