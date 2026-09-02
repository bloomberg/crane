From Stdlib Require Import List.
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.

Module HktNullaryMethodTyarg.

(** [emptyc] takes no value argument, so its element type is not deducible and
    must be passed explicitly.  The generic body omits it:

      return sizec<_tcI0>(addc<_tcI0>(x, addc<_tcI0>(y, emptyc<_tcI0>())));

    error: no matching function for call to 'emptyc'
    (the wrapper is declared template <Coll _tcI0, typename T2>) *)

Class Coll (C : Type -> Type) := {
  emptyc : forall A : Type, C A ;
  addc : forall A : Type, A -> C A -> C A ;
  sizec : forall A : Type, C A -> nat
}.
Arguments emptyc {C _ A}.
Arguments addc {C _ A} _ _.
Arguments sizec {C _ A} _.

Fixpoint llen {A} (l : list A) : nat :=
  match l with nil => 0 | cons _ r => S (llen r) end.

Instance LC : Coll list := {
  emptyc := fun A => @nil A ;
  addc := fun A x l => cons x l ;
  sizec := fun A l => llen l
}.

Definition two {C} `{Coll C} {A} (x y : A) : nat := sizec (addc x (addc y emptyc)).

Definition run : nat := @two list _ nat 1 2.

End HktNullaryMethodTyarg.

Crane Extraction "hkt_nullary_method_tyarg" HktNullaryMethodTyarg.run.
