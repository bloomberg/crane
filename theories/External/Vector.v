(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Monads.ITree Monads.IO.

Axiom vector : Type -> Type.

Module Vector_axioms.
  Import IO_axioms.
  Axiom iemptyVec : forall (A : Type), iIO (vector A).
  Axiom iget : forall {A}, vector A -> int -> iIO A.
  Axiom ipush : forall {A}, vector A -> A -> iIO void.
  Axiom ipop : forall {A}, vector A -> iIO void.
  Axiom isize : forall {A}, vector A -> iIO int.
  Axiom iisEmpty : forall {A}, vector A -> iIO bool.
  Axiom iassign : forall {A}, vector A -> int -> A -> iIO (vector A).

End Vector_axioms.

Crane Extract Skip Module Vector_axioms.
Import Vector_axioms.

Definition emptyVec (A : Type) : IO (vector A) := trigger (iemptyVec A).
Definition get {A} (v  : vector A) (x : int) : IO A := trigger (iget v x).
Definition push {A} (v  : vector A) (a : A) : IO void := trigger (ipush v a).
Definition pop {A} (v  : vector A) : IO void := trigger (ipop v).
Definition size {A} (v  : vector A) : IO int := trigger (isize v).
Definition isEmpty {A} (v  : vector A) : IO bool := trigger (iisEmpty v).
Definition assign {A} (v  : vector A) (x : int) (a : A) : IO (vector A) := trigger (iassign v x a).

(* What if emptyVec wasn't monadic, and get and push etc... took prop args that are generated from monads? *)

Crane Extract Inlined Constant vector => "std::vector<%t0>" From "vector".
Crane Extract Inlined Constant emptyVec => "{}".
Crane Extract Inlined Constant get => "%a0.at(%a1)".
Crane Extract Inlined Constant push => "%a0.push_back(%a1)".
Crane Extract Inlined Constant pop => "%a0.pop_back()".
Crane Extract Inlined Constant size => "%a0.size()".
Crane Extract Inlined Constant isEmpty => "%a0.empty()".
Crane Extract Inlined Constant assign => "%a0.assign(%a1, %a2)".
