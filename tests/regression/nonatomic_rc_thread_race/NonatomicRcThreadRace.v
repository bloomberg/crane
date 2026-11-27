(* [Set Crane NonAtomicRc] is a promise that the extracted program is
   single-threaded, so its reference counts need no atomics.  This unit breaks
   that promise: it also uses [Monads.Thread], and two spawned threads share an
   inductive value, so a non-atomic count would be lost and the cells freed
   while still reachable.

   Crane does not take the promise on trust.  A unit that reaches a custom
   extraction spelled in terms of <thread> keeps [std::shared_ptr], and says so
   with the [crane-non-atomic-rc-concurrent] warning.  The program below is
   pure and uses no axioms; it must run cleanly under the sanitizers. *)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt Monads.ITree Monads.IO Monads.Thread.
Open Scope itree_scope.
Set Crane NonAtomicRc.

Module NonatomicRcThreadRace.

  Inductive lst : Set := Nil : lst | Cons : nat -> lst -> lst.

  Fixpoint build (n : nat) : lst :=
    match n with O => Nil | S k => Cons k (build k) end.

  Fixpoint len (l : lst) : nat :=
    match l with Nil => 0 | Cons _ r => S (len r) end.

  (** Shared between both threads; every [step] copies it. *)
  Definition shared : lst := build 4.

  Definition step (l : lst) : nat := len (Cons 0 l).

  Fixpoint churn (n : nat) (l : lst) : nat :=
    match n with O => 0 | S k => step l + churn k l end.

  Fixpoint worker (n : nat) : itree concE unit :=
    match n with
    | 0 => Ret tt
    | S k =>
      (if Nat.eqb (churn 2000 shared) 0 then print_endline "unreachable"
       else Ret tt) ;;
      worker k
    end.

  Definition test : itree concE unit :=
    t1 <- spawn worker 200 ;;
    t2 <- spawn worker 200 ;;
    join t1 ;;
    join t2 ;;
    Ret tt.

  Definition run (u : unit) : unit := run_conc test.

End NonatomicRcThreadRace.

Crane Extraction "nonatomic_rc_thread_race" NonatomicRcThreadRace.
