From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module PolyIdAtFunctionType.

(** A polymorphic identity instantiated at a function type collapses the
    two levels of application into a single call on a one-argument
    [std::function]. *)
Definition id2 {A : Type} (x : A) : A := x.

Definition apply_id (n : nat) : nat := id2 (fun k : nat => k + 1) n.

Definition apply_id2 (n : nat) : nat :=
  id2 (A := (nat -> nat) -> nat -> nat) (fun f x => f (f x))
      (id2 (fun k : nat => k * 3)) n.

Definition total : nat := apply_id 4 + apply_id2 2.

End PolyIdAtFunctionType.
Crane Extraction "poly_id_at_function_type" PolyIdAtFunctionType.
