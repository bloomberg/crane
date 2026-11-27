
From Stdlib Require Import
  Arith.PeanoNat
  Strings.String
.

From Crane Require Monads.ST.
From Crane Require Import
  Monads.Error
  Monads.ITree
.

From ExtLib Require Import
  Data.Monads.EitherMonad
  Structures.Maps
.

From ITree Require Import
  Events.Exception
  ITree
  ITreeFacts
.

Import Monads.
Local Open Scope monad_scope.

Section FibstCofixRepro.

  Context {R : ST.Refs}.

  Let V : nat -> Type := fun _ => nat.
  Let E0 := (ST.Event R V) +' exceptE Err.

  (** Reproduces a version of fibST in STtest.v.  It recurses without
      end by construction: [n] is not decremented on each recursive call.
      The test checks that the divergence is a constant-stack loop.

      Extraction used to fail with "a type mapped to nothing reached the
      printer: ST.Event".  Three defects: the section's [Let]s are [let]s at
      the head of the body, and [db_from_rel_context] numbered them as type
      variables, so the annotation of [go] named no variable of the
      declaration and seeded nothing; a [let cofix] was not seeded from its
      annotation at all (only a [let fix] was); and seeding opened every
      [Unknown] of an annotation to a meta, including the argument the
      unapplied family [ST.Event ... +' exceptE Err] is eta-expanded at,
      which nothing solves.  The open metas generalised into type variables
      of [go]'s own, so [go] was lifted to a template whose call spelled the
      skipped [ST.Event].  Then, generated in place, [Core_plan.Closures]
      took [go] to escape, as a cofixpoint's body is suspended -- but a
      cofixpoint into a monad generated as sequencing is not. *)
  Definition fibst_repro (n : nat) : itree E0 nat :=
    let cofix go (x y : ST.ref nat) : itree E0 nat :=
      match n with
      | 0 => ST.read_ref (E := E0) (V := V) x
      | Datatypes.S n =>
          x' <- ST.read_ref (E := E0) (V := V) x;;
          y' <- ST.read_ref (E := E0) (V := V) y;;
          ST.write_ref (E := E0) (V := V) x y';;
          ST.write_ref (E := E0) (V := V) y (x' + y');;
          Tau (go x y)
      end in
    if (Nat.leb n 2)
    then Ret n
    else
      x <- ST.new_ref (E := E0) (V := V) 0;;
      y <- ST.new_ref (E := E0) (V := V) 1;;
      go x y.

End FibstCofixRepro.

Module FibstCofixReproTests.
  Definition fibst_repro := @fibst_repro ST.cpp_refs.
End FibstCofixReproTests.

Require Import Crane.Mapping.NatInt.

Set Crane Loopify.

Crane Extraction "fibst_cofix_repro" FibstCofixReproTests.
