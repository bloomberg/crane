From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.
Set Crane BoxedFields.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    A mutual fixpoint returning [sum (st nat) (option tree)] (with [st A := nat -> A * nat]) through a local fixpoint over [list (st pt)]: instantiating a [requires] clause in theories/cpp/obj.h fails, "substitution into constraint expression resulted in a non-constant expression". *)
Module ConstraintSubstitutionObj.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Record pt : Type := mkpt { px : nat; py : bool }.
Fixpoint tree_obs (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r => (tree_obs l * 7 + v + tree_obs r * 3) mod 10007
  end.
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.
#[global] Instance sz_bool : Sz bool := { sz b := if b then 1 else 0 }.
#[global] Instance sz_pair {A B : Type} `{Sz A} `{Sz B} : Sz (A * B) :=
  { sz p := (sz (fst p) * 3 + sz (snd p)) mod 10007 }.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Class Mon (A : Type) := { munit : A; mop : A -> A -> A }.
#[global] Instance mon_bool : Mon bool := { munit := false; mop := orb }.
Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Fixpoint h2a (n5 : nat) : Z :=
  0%Z
with h2b (n36 : nat) : (sum (st nat) (option tree)) :=
  match n36 with O => (if (fold_left (fun (acc37 : bool) (e38 : nat) => (mop acc37 acc37)) (if false then [2%nat; 4%nat; 158%nat] else (@nil nat)) (match n36 with O => true | S m39 => true end)) then (@inr (st nat) (option tree) (match n36 with O => (@None tree) | S m40 => (Some Leaf) end)) else (let fix go41 (l42 : (list (st pt))) (acc43 : (sum (st nat) (option tree))) {struct l42} : (sum (st nat) (option tree)) := match l42 with [] => (if true then (@inr (st nat) (option tree) (@None tree)) else acc43) | e44 :: rest45 => go41 rest45 (match n36 with O => (@inl (st nat) (option tree) (sret 7%nat)) | S m46 => acc43 end) end in go41 (flat_map (fun y47 : nat => (@nil (st pt))) (@nil nat)) (@inr (st nat) (option tree) (Some Leaf)))) | S m48 => (let x49 := (match (h2a m48) with Z0 => (sz (7%nat, true)) | Zpos _ => (fold_left (fun (acc50 : nat) (e51 : bool) => 0%nat) (@nil bool) m48) | Zneg _ => 9%nat end) in (@inr (st nat) (option tree) (let x52 := x49 in (Some Leaf))))
  end.
End ConstraintSubstitutionObj.

Crane Extraction "constraint_substitution_obj" ConstraintSubstitutionObj.
