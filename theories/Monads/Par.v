(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Parallel computation monad using [std::async] / [std::future].

    [Par S z A] tracks a phantom resource type [S] and an integer cost [z].
    [runPar] erases the wrapper and returns the result.
    Threads are created with [mk_thread] and joined with [get_thread]. *)
From Corelib Require Import PrimInt63 Sint63Axioms PrimString.
From Stdlib Require Import ZArith.
From Crane Require Extraction.
From Crane Require Mapping.Std.

Open Scope int63.

Axiom Par : forall (S : Type) {z : int}, Type -> Type.
Axiom Pret : forall {S A}, A -> @Par S 0 A.
Axiom Pbind : forall {S x y A B}, @Par S x A -> (A -> @Par S y B)-> @Par S (add x y) B.
Axiom runPar : forall {A}, (forall S, @Par S 0 A) -> A.

Axiom thread : Type -> Type -> Type.
Axiom mk_thread  : forall {S A B}, (A -> B) -> A -> @Par S 1 (thread S B).
Axiom get_thread : forall {S B}, thread S B -> @Par S (PrimInt63.sub 0 1) B. (* BAD: Can get the same thread twice!! *)

(* Axiom mk_thread  : forall {S A B}, (A -> B) -> A -> @Par S [A] Unit.
Axiom thread_term : forall {S n}, Fin n -> @Par S n (Thread S (nth )).
Axiom get_thread : forall {S B}, Fin n -> @Par S (PrimInt63.sub 0 1) B. *)

Crane Extract Monad Par [ bind := Pbind , ret := Pret ] =>  "%t1".
Crane Extract Inlined Constant runPar => "%a0".
Crane Extract Inlined Constant thread => "std::future<%t1>" From "future".
Crane Extract Inlined Constant mk_thread => "std::async(std::launch::async, %a0, %a1)".
Crane Extract Inlined Constant get_thread => "%a0.get()".

Module ParNotations.

  Declare Scope Parmonad_scope.
  Delimit Scope Parmonad_scope with Parmonad.
  Open Scope Parmonad.

  Notation "e1 ;; e2" := (@Pbind _ _ _ _ _ e1%Parmonad (fun _ => e2%Parmonad))
    (at level 61, right associativity) : Parmonad_scope.
  Notation "x <- c1 ;; c2" := (@Pbind _ _ _ _ _ c1%Parmonad (fun x => c2%Parmonad))
    (at level 61, c1 at next level, right associativity) : Parmonad_scope.

End ParNotations.
Import ParNotations.
