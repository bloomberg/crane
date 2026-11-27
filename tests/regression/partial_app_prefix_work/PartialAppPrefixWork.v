(** A definition that computes before taking all the parameters its type
    gives it: [mk fs] folds once and returns the closure.  Applied partially
    and bound or passed as a value, the fold must run where the partial
    application stands, once, as in Rocq, not again at every application of
    the closure. *)
From Stdlib Require Import List.
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.
Import ListNotations.

Module PartialAppPrefixWork.

Definition compose {A : Type} (f g : A -> A) : A -> A := fun x => f (g x).

Definition mk (fs : list (nat -> nat)) : nat -> nat := fold_right compose (fun x => x) fs.

(** Polymorphic, so the copy is read at the use's type argument. *)
Definition mkp {A : Type} (fs : list (A -> A)) : A -> A := fold_right compose (fun x => x) fs.

(** Its body is a partial application of [mk], which computes as well. *)
Definition mk2 (fs : list (nat -> nat)) : nat -> nat := mk (map (fun f x => f (f x)) fs).

(** A let before the closure. *)
Definition shifted (k : nat) (fs : list (nat -> nat)) : nat -> nat :=
  let g := mk fs in fun x => g (x + k).

Definition fs3 : list (nat -> nat) := [fun x => x + 1; fun x => x * 2; fun x => x + 3].

Definition run (n : nat) : nat :=
  let g := mk fs3 in
  let h := mkp fs3 in
  let k := mk2 fs3 in
  let s := shifted 5 fs3 in
  fold_left (fun acc i => acc + g i + h i + k i + s i + mk fs3 i) (seq 0 n) 0
  + fold_left (fun acc x => acc + x) (map (mk fs3) (seq 0 n)) 0.

End PartialAppPrefixWork.

Crane Extraction "partial_app_prefix_work" PartialAppPrefixWork.
