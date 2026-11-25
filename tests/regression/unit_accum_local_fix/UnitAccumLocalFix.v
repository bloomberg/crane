(** A local fixpoint whose result is [unit] (directly or under a sequential
    monad) is a lambda returning [void]: every [return] in it, including the
    one handing back a [unit] accumulator, returns nothing. *)
From Stdlib Require Import Arith.PeanoNat List.
From Stdlib Require PrimString.
From ITree Require Import Events.Exception ITree.
From Crane Require Import Mapping.NatIntStd Monads.Error Monads.ITree Monads.STMonad.
From Crane Require Extraction.
Import Monads. Import ListNotations. Local Open Scope monad_scope.

Section S.
  Context {R : STRefs}.
  Notation E0 := (STEvent R (fun _ : nat => nat) +' exceptE Err).

  (** [for_each_with] at [B := unit], unfolded below into a local fixpoint. *)
  Definition fill (n : nat) : itree E0 nat :=
    a <- newArray n 0;;
    for_each_with (seq 0 n) tt (fun _ i => writeArray a i (i * 2));;
    readArray a (n - 1).

End S.

Module UnitAccumLocalFix.
  Definition fill := Eval unfold fill, for_each_with in @fill cpp_refs.

  (** [for_each_with] at [B := unit] as a top-level [Fixpoint]. *)
  Fixpoint each_unit (xs : list nat) (u : unit)
    (f : unit -> nat -> itree (STEvent cpp_refs (fun _ : nat => nat) +' exceptE Err) unit)
    : itree (STEvent cpp_refs (fun _ : nat => nat) +' exceptE Err) unit :=
    match xs with
    | nil => Ret u
    | i :: t => u' <- f u i;; each_unit t u' f
    end.

  Definition fill_top (n : nat) : itree (STEvent cpp_refs (fun _ : nat => nat) +' exceptE Err) nat :=
    a <- newArray n 0;;
    each_unit (seq 0 n) tt (fun _ i => writeArray a i (i * 3));;
    readArray a (n - 1).

  (** A pure top-level [Fixpoint] returning its [unit] accumulator. *)
  Fixpoint walk_top (xs : list nat) (u : unit) : unit :=
    match xs with
    | nil => u
    | _ :: t => walk_top t u
    end.

  (** A pure local fixpoint returning its [unit] accumulator. *)
  Definition walk (l : list nat) : unit :=
    (fix go (xs : list nat) (u : unit) : unit :=
       match xs with
       | nil => u
       | _ :: t => go t u
       end) l tt.

  (** The [unit] result of a local fixpoint used as a value. *)
  Definition walk_pair (l : list nat) : unit * nat :=
    let u := (fix go (xs : list nat) (u : unit) : unit :=
                match xs with
                | nil => u
                | _ :: t => go t u
                end) l tt in
    (u, length l).

  (** A [unit]-returning local fixpoint called twice, so held as a closure. *)
  Definition walk_twice (l : list nat) : unit * unit :=
    let g := fix go (xs : list nat) (u : unit) : unit :=
               match xs with
               | nil => u
               | _ :: t => go t u
               end in
    (g l tt, g (rev l) tt).

  (** A [unit] accumulator threaded beside a [nat] one. *)
  Definition sum_with_unit (l : list nat) : nat :=
    (fix go (xs : list nat) (u : unit) (acc : nat) : nat :=
       match xs with
       | nil => acc
       | x :: t => go t u (acc + x)
       end) l tt 0.
End UnitAccumLocalFix.

Crane Extraction "unit_accum_local_fix" UnitAccumLocalFix.
