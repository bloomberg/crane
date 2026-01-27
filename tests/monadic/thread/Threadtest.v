(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.Thread.

Import ConcNotations.

Module threadtest.

  Fixpoint fun1 (n : nat)  : Conc void :=
    match n with
    | 0 => print_endline "fun1 is done!!!" ;;
           Cret ghost
    | S n => print_endline "fun1 is sleeping for 100ms" ;;
             sleep 100%int63 ;;
             fun1 n
    end.

  Fixpoint fun2 (n : nat) : Conc void :=
    match n with
    | 0 => print_endline "fun2 is done!!!" ;;
           Cret ghost
    | S n => print_endline "fun2 is sleeping for 150ms" ;;
             sleep 150%int63 ;;
             fun2 n
    end.

  Definition test (m n : nat) : Conc void :=
    t1 <- mk_thread fun1 m ;;
    t2 <- mk_thread fun2 n ;;
    join t1 ;;
    join t2 ;;
    Cret ghost.

  Definition test2 (m n : nat) : void := Ceval (test m n).

End threadtest.

Crane Extraction "thread" threadtest.
