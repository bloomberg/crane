(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Mutable vector effects for the standard library flavor.

    Provides axioms for [std::vector] operations as IO effects.
    Smart constructors produce [itree ioE] computations. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

Axiom vector : Type -> Type.

Module Vector_axioms.
  Axiom iemptyVec : forall (A : Type), ioE (vector A).
  Axiom iget : forall {A}, vector A -> int -> ioE A.
  Axiom ipush : forall {A}, vector A -> A -> ioE unit.
  Axiom ipop : forall {A}, vector A -> ioE unit.
  Axiom isize : forall {A}, vector A -> ioE int.
  Axiom iisEmpty : forall {A}, vector A -> ioE bool.
  Axiom iassign : forall {A}, vector A -> int -> A -> ioE (vector A).

End Vector_axioms.

Crane Extract Skip Module Vector_axioms.
Import Vector_axioms.

Definition emptyVec (A : Type) : itree ioE (vector A) := ITree.trigger (iemptyVec A).
Definition get {A} (v : vector A) (x : int) : itree ioE A := ITree.trigger (iget v x).
Definition push {A} (v : vector A) (a : A) : itree ioE unit := ITree.trigger (ipush v a).
Definition pop {A} (v : vector A) : itree ioE unit := ITree.trigger (ipop v).
Definition size {A} (v : vector A) : itree ioE int := ITree.trigger (isize v).
Definition isEmpty {A} (v : vector A) : itree ioE bool := ITree.trigger (iisEmpty v).
Definition assign {A} (v : vector A) (x : int) (a : A) : itree ioE (vector A) := ITree.trigger (iassign v x a).

Crane Extract Inlined Constant vector => "std::vector<%t0>" From "vector".
Crane Extract Inlined Constant emptyVec => "{}".
Crane Extract Inlined Constant get => "%a0.at(%a1)".
Crane Extract Inlined Constant push => "%a0.push_back(%a1)".
Crane Extract Inlined Constant pop => "%a0.pop_back()".
Crane Extract Inlined Constant size => "%a0.size()".
Crane Extract Inlined Constant isEmpty => "%a0.empty()".
Crane Extract Inlined Constant assign => "%a0.assign(%a1, %a2)".
