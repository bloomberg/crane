(** [Set Crane Reuse] with [Set Crane NonAtomicRc] in a unit that spawns
    threads.  The request is withheld from such a unit, so no cell is
    recycled here; but which parameters a function owns is settled once for
    the whole program, before any unit decides whether it is concurrent.

    [churn] matches on [n], and its [O] arm rebuilds [O]: a reuse candidate.
    Whether that makes [n] owned must not depend on the unit's concurrency,
    or the parameters settled for the program and the ones its body reads at
    generation disagree (a [CRANE_CHECK_IR] violation).  Both read the
    program-wide request. *)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.Thread.
Open Scope itree_scope.
Set Crane NonAtomicRc.
Set Crane Reuse.

Module ReuseSummaryConcurrentUnit.

  Inductive lst : Set := Nil : lst | Cons : nat -> lst -> lst.

  Fixpoint build (n : nat) : lst :=
    match n with O => Nil | S k => Cons k (build k) end.

  Fixpoint len (l : lst) : nat :=
    match l with Nil => 0 | Cons _ r => S (len r) end.

  Definition shared : lst := build 4.

  Definition step (l : lst) : nat := len (Cons 0 l).

  Fixpoint churn (n : nat) (l : lst) : nat :=
    match n with O => 0 | S k => step l + churn k l end.

  Definition total : nat := churn 3 shared.

  Fixpoint worker (n : nat) : itree concE unit :=
    match n with
    | 0 => Ret tt
    | S k =>
      (if Nat.eqb (churn 200 shared) 0 then print_endline "unreachable"
       else Ret tt) ;;
      worker k
    end.

  Definition test : itree concE unit :=
    t1 <- spawn worker 20 ;;
    t2 <- spawn worker 20 ;;
    join t1 ;;
    join t2 ;;
    Ret tt.

  Definition run (u : unit) : unit := runConc test.

End ReuseSummaryConcurrentUnit.

Crane Extraction "reuse_summary_concurrent_unit" ReuseSummaryConcurrentUnit.
