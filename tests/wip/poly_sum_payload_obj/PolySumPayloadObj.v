From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    In a constrained polymorphic definition, [pmap] over a [ptree (sum tree A)] literal holding [inr a20] builds [Sum<crane::obj, ...>] where a [uint64_t] is expected ("no viable conversion from 'Sum<crane::obj, unsigned long long>'"). *)
Module PolySumPayloadObj.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Record pt : Type := mkpt { px : nat; py : bool }.
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Arguments PLeaf {A}.
Arguments PNode {A} _ _ _.
Fixpoint pmap {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
  match t with PLeaf => PLeaf | PNode l x r => PNode (pmap f l) (f x) (pmap f r) end.
Fixpoint pfold {A B : Type} (f : B -> A -> B) (t : ptree A) (acc : B) : B :=
  match t with PLeaf => acc | PNode l x r => pfold f r (f (pfold f l acc) x) end.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Definition f2 {A : Type} `{Sz A} (a20 : A) (a21 : (nat -> (st pt))) (a22 : (ptree bool)) : string :=
  (String.substring (0%nat mod 4) ((pfold (fun (pa32 : nat) (px33 : nat) => 0%nat mod 1000) (pmap (fun y31 : (sum tree A) => 0%nat) (PNode (@PLeaf (sum tree A)) (@inr tree A a20) (@PLeaf (sum tree A)))) 0%nat) mod 4) ""%string).

Definition t_5 : nat :=
  ((fun w111 : string => String.length w111 * 13 + (match String.get 0 w111 with Some c => Ascii.nat_of_ascii c | None => 0 end)) (f2 0%nat (fun _ : nat => (sret (mkpt 0 true))) (@PLeaf bool))).
End PolySumPayloadObj.

Crane Extraction "poly_sum_payload_obj" PolySumPayloadObj.
