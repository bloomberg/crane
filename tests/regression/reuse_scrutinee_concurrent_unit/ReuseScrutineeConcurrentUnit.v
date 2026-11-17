(** Under [Set Crane Reuse], a parameter a function matches on and rebuilds
    from is passed owned, so the rebuilt value can take the matched cells --
    for an ordinary inductive only under non-atomic counts.  Which parameters
    are owned is settled once for the whole program, before any unit decides
    whether it starts a thread; this unit asks for [NonAtomicRc] and starts
    threads, so it is refused the request.  Its parameters are owned as
    requested all the same, and it recycles nothing: under [CRANE_CHECK_IR]
    the settled ownership of [churn] must be what its body reads, which it
    was not while the body was read against the unit's refusal. *)
From Corelib Require Import PrimInt63 PrimString.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Monads.ITree Monads.IO Monads.Thread.
Open Scope itree_scope.
Set Crane NonAtomicRc.
Set Crane Reuse.

Module ReuseScrutineeConcurrentUnit.

  Inductive lst : Set := Nil : lst | Cons : nat -> lst -> lst.

  Fixpoint build (n : nat) : lst :=
    match n with O => Nil | S k => Cons k (build k) end.

  Fixpoint len (l : lst) : nat :=
    match l with Nil => 0 | Cons _ r => S (len r) end.

  Definition shared : lst := build 4.

  (** Matches on [n] and rebuilds [O] in the [O] branch: a reuse candidate. *)
  Fixpoint churn (n : nat) (l : lst) : nat :=
    match n with O => 0 | S k => len (Cons 0 l) + churn k l end.

  Fixpoint worker (n : nat) : itree concE unit :=
    match n with
    | 0 => Ret tt
    | S k =>
      (if Nat.eqb (churn 100 shared) 500 then Ret tt
       else print_endline "wrong total") ;;
      worker k
    end.

  Definition test : itree concE unit :=
    t1 <- spawn worker 20 ;;
    t2 <- spawn worker 20 ;;
    join t1 ;;
    join t2 ;;
    Ret tt.

  Definition run (u : unit) : unit := runConc test.

  Definition total (u : unit) : nat := churn 10 shared.

End ReuseScrutineeConcurrentUnit.

Crane Extraction "reuse_scrutinee_concurrent_unit" ReuseScrutineeConcurrentUnit.
