(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.Thread.

Open Scope itree_scope.

Module threadtest.

  Fixpoint fun1 (n : nat) : itree concE unit :=
    match n with
    | 0 => print_endline "fun1 is done!!!" ;;
           Ret tt
    | S n => print_endline "fun1 is sleeping for 100ms" ;;
             sleep 100%int63 ;;
             fun1 n
    end.

  Fixpoint fun2 (n : nat) : itree concE unit :=
    match n with
    | 0 => print_endline "fun2 is done!!!" ;;
           Ret tt
    | S n => print_endline "fun2 is sleeping for 150ms" ;;
             sleep 150%int63 ;;
             fun2 n
    end.

  Definition test (m n : nat) : itree concE unit :=
    t1 <- spawn fun1 m ;;
    t2 <- spawn fun2 n ;;
    join t1 ;;
    join t2 ;;
    Ret tt.

  Definition test_pure (m n : nat) : unit := runConc (test m n).

End threadtest.

Crane Extraction "thread" threadtest.
