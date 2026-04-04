(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   Regression test for ITree-based effect composition.

   Verifies that [parE] and [consoleE] compose correctly via [+']
   and generate valid C++ with both [std::async] and [std::cout].
*)
From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd
                          Monads.ITree Monads.IO Monads.Par.

Module EffectCompose.

  (** Composed effect: parallel + console. *)
  Definition parIOE := parE +' consoleE.
  Crane Extract Skip parIOE.

  (** Spawn a future that doubles a number, retrieve the result. *)
  Definition par_double (n : nat) : itree parIOE nat :=
    let double (x : nat) := x + x in
    t <- async double n ;;
    get_thread t.

  (** Use parE to compute two values in parallel and add them. *)
  Definition par_add (a b : nat) : itree parIOE nat :=
    let double (x : nat) := x + x in
    t1 <- async double a ;;
    t2 <- async double b ;;
    r1 <- get_thread t1 ;;
    r2 <- get_thread t2 ;;
    Ret (r1 + r2).

  (** Parallel computation with IO: compute then print. *)
  Definition par_compute_and_greet (n : nat) : itree parIOE nat :=
    let succ (x : nat) := x + 1 in
    print_endline "computing..." ;;
    t <- async succ n ;;
    result <- get_thread t ;;
    print_endline "done" ;;
    Ret result.

End EffectCompose.

Crane Extraction "effect_compose" EffectCompose.
