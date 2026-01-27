(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.ArrayStd.
From Corelib Require Import PrimInt63.

Module Vec.

Open Scope int63.

Definition test1 : array int 5 := make 5 12.
Definition test2 := length test1.
Definition test3 := get_nth test1 3.
Definition test4 : array int 5 := set_nth test1 2 14.


(*
Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall (n : nat), A -> vec A n -> vec A (S n).

Arguments vnil {A}.
Arguments vcons {A} n x xs.

Fixpoint vmap {A B : Type} {n : nat} (f : A -> B) (v : vec A n) : vec B n.
Proof.
  destruct v as [|n x xs].
  - left.
  - right.
    exact (f x).
    exact (@vmap _ _ _ f xs).
Defined.

Fixpoint vapp {A : Type} {n m : nat} (v1 : vec A n) (v2 : vec A m) : vec A (n + m).
Proof.
  destruct v1 as [|n x xs].
  - exact v2.
  - right.
    exact x.
    exact (@vapp _ _ _ xs v2).
Defined.
*)
End Vec.

Crane Extraction "vec" Vec.
