(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Mutable vector effects for the BDE flavor.

    Provides axioms for [bsl::vector] operations as IO effects.
    Smart constructors produce [itree iIO] computations. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.ITree Monads.IOBDE.

Axiom vector : Type -> Type.

Module Vector_axioms.
  Axiom iemptyVec : forall (A : Type), iIO (vector A).
  Axiom iget : forall {A}, vector A -> int -> iIO A.
  Axiom ipush : forall {A}, vector A -> A -> iIO unit.
  Axiom ipop : forall {A}, vector A -> iIO unit.
  Axiom isize : forall {A}, vector A -> iIO int.
  Axiom iisEmpty : forall {A}, vector A -> iIO bool.
  Axiom iassign : forall {A}, vector A -> int -> A -> iIO (vector A).
End Vector_axioms.

Crane Extract Skip Module Vector_axioms.
Import Vector_axioms.

Definition emptyVec (A : Type) : itree iIO (vector A) := ITree.trigger (iemptyVec A).
Definition get {A} (v : vector A) (x : int) : itree iIO A := ITree.trigger (iget v x).
Definition push {A} (v : vector A) (a : A) : itree iIO unit := ITree.trigger (ipush v a).
Definition pop {A} (v : vector A) : itree iIO unit := ITree.trigger (ipop v).
Definition size {A} (v : vector A) : itree iIO int := ITree.trigger (isize v).
Definition isEmpty {A} (v : vector A) : itree iIO bool := ITree.trigger (iisEmpty v).
Definition assign {A} (v : vector A) (x : int) (a : A) : itree iIO (vector A) := ITree.trigger (iassign v x a).

Crane Extract Inlined Constant vector => "bsl::vector<%t0>" From "bsl_vector.h".
Crane Extract Inlined Constant emptyVec => "{}".
Crane Extract Inlined Constant get => "%a0.at(%a1)".
Crane Extract Inlined Constant push => "%a0.push_back(%a1)".
Crane Extract Inlined Constant pop => "%a0.pop_back()".
Crane Extract Inlined Constant size => "%a0.size()".
Crane Extract Inlined Constant isEmpty => "%a0.empty()".
Crane Extract Inlined Constant assign => "%a0.assign(%a1, %a2)".
