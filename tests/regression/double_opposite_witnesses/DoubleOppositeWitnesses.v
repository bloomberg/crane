(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: double-opposite witness packaging with functor records and Type-valued paths. *)

From Stdlib Require Import Nat.

Module DoubleOppositeWitnessesCase.

Inductive Path {A : Type} (x : A) : A -> Type :=
| path_refl : Path x x.

Arguments path_refl {_ _}.

Definition path_code {A : Type} {x y : A} (p : Path x y) : nat :=
  match p with
  | path_refl => 1
  end.

Record PreCategory := {
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  identity : forall X : Obj, Hom X X;
  compose : forall X Y Z : Obj, Hom Y Z -> Hom X Y -> Hom X Z
}.

Arguments Obj _ : clear implicits.
Arguments Hom _ _ _ : clear implicits.
Arguments identity {_} _.
Arguments compose {_} _ _ _ _ _.

Definition opposite_category (C : PreCategory) : PreCategory :=
  {| Obj := Obj C;
     Hom := fun X Y => Hom C Y X;
     identity := fun X => @identity C X;
     compose := fun X Y Z f g => @compose C Z Y X g f |}.

Record Functor (C D : PreCategory) := {
  object_of : Obj C -> Obj D;
  morphism_of : forall X Y : Obj C, Hom C X Y -> Hom D (object_of X) (object_of Y)
}.

Arguments object_of {_ _} _ _.
Arguments morphism_of {_ _} _ _ _ _.

Definition compose_functor {A B C : PreCategory}
    (F : Functor B C)
    (G : Functor A B)
    : Functor A C.
Proof.
  refine
    {| object_of := fun X => object_of F (object_of G X);
       morphism_of :=
         fun X Y f =>
           morphism_of F (object_of G X) (object_of G Y) (morphism_of G X Y f) |}.
Defined.

Record PreStableCategory := {
  base_category : PreCategory;
  zero_object : Obj base_category;
  suspension : Obj base_category -> Obj base_category
}.

Arguments base_category _ : clear implicits.
Arguments zero_object _ : clear implicits.
Arguments suspension _ _ : clear implicits.

Definition opposite_prestable_category (PS : PreStableCategory) : PreStableCategory :=
  {| base_category := opposite_category (base_category PS);
     zero_object := zero_object PS;
     suspension := fun X => suspension PS X |}.

Definition nat_category : PreCategory :=
  {| Obj := nat;
     Hom := fun _ _ => nat;
     identity := fun X => X;
     compose := fun _ _ _ f g => f + g |}.

Definition toy_prestable : PreStableCategory :=
  {| base_category := nat_category;
     zero_object := 0;
     suspension := S |}.

Definition into_double_opposite_functor (C : PreCategory)
    : Functor C (opposite_category (opposite_category C)).
Proof.
  refine
    (@Build_Functor C (opposite_category (opposite_category C))
      (fun X => X)
      _).
  intros X Y f.
  exact f.
Defined.

Definition out_of_double_opposite_functor (C : PreCategory)
    : Functor (opposite_category (opposite_category C)) C.
Proof.
  refine
    (@Build_Functor (opposite_category (opposite_category C)) C
      (fun X => X)
      _).
  intros X Y f.
  exact f.
Defined.

Definition duality_involution (PS : PreStableCategory)
  : {F : Functor (base_category PS)
         (base_category (opposite_prestable_category
                          (opposite_prestable_category PS))) &
     {G : Functor (base_category (opposite_prestable_category
                                   (opposite_prestable_category PS)))
       (base_category PS) &
       ((forall X : Obj (base_category PS),
           Path (object_of (compose_functor G F) X) X) *
        (forall X : Obj (base_category (opposite_prestable_category
                                         (opposite_prestable_category PS))),
           Path (object_of (compose_functor F G) X) X))%type }}.
Proof.
  refine (existT _ (into_double_opposite_functor (base_category PS)) _).
  refine (existT _ (out_of_double_opposite_functor (base_category PS)) _).
  split.
  - intro X.
    exact path_refl.
  - intro X.
    exact path_refl.
Defined.

Definition toy_duality_involution := duality_involution toy_prestable.

Definition forward_functor := projT1 toy_duality_involution.
Definition backward_package := projT2 toy_duality_involution.
Definition backward_functor := projT1 backward_package.
Definition identity_witnesses := projT2 backward_package.

Definition forward_object_7 : nat :=
  object_of forward_functor 7.

Definition backward_object_9 : nat :=
  object_of backward_functor 9.

Definition forward_morphism_3 : nat :=
  morphism_of forward_functor 4 7 3.

Definition roundtrip_left_11 : nat :=
  object_of (compose_functor backward_functor forward_functor) 11.

Definition roundtrip_right_13 : nat :=
  object_of (compose_functor forward_functor backward_functor) 13.

Definition roundtrip_morphism_5 : nat :=
  morphism_of (compose_functor backward_functor forward_functor) 2 9 5.

Definition left_identity_code_11 : nat :=
  path_code ((fst identity_witnesses) 11).

Definition right_identity_code_13 : nat :=
  path_code ((snd identity_witnesses) 13).

Definition suspended_zero : nat :=
  suspension toy_prestable (zero_object toy_prestable).

End DoubleOppositeWitnessesCase.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.

Crane Extraction "double_opposite_witnesses" DoubleOppositeWitnessesCase.
