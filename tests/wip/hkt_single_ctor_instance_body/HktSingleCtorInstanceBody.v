From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module HktSingleCtorInstanceBody.

(** A single-constructor inductive is generated as a plain struct with no
    [variant_t] and no [v()].  An instance method whose body pattern-matches on
    it is still emitted in variant style, against the erased carrier:

      error: use of undeclared identifier 'Mkbox'
      error: no member named 'v' in 'box<std::any>' *)

Class Ftor (F : Type -> Type) := { fmap : forall A B : Type, (A -> B) -> F A -> F B }.
Class Pointed (F : Type -> Type) `{Ftor F} := { pnt : forall A : Type, A -> F A }.
Arguments fmap {F _ A B} _ _.
Arguments pnt {F _ _ A} _.

Inductive box (A : Type) : Type := mkbox : A -> box A.
Arguments mkbox {A} _.

Instance FB : Ftor box := {
  fmap := fun A B f b => match b with mkbox x => mkbox (f x) end
}.
Instance PB : Pointed box := { pnt := fun A x => mkbox x }.

Definition liftme {F} `{Pointed F} (n : nat) : F nat := pnt n.

Definition run (n : nat) : box nat := liftme n.

End HktSingleCtorInstanceBody.

Crane Extraction "hkt_single_ctor_instance_body" HktSingleCtorInstanceBody.run.
