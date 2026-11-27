From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated program, shrunk by ephyra and delta-reduced
    (unrelated-looking declarations kept are needed for the trigger).

    A mutual fixpoint returning [st (ptree nat)] through a local fixpoint seeded with the recursive call, next to a fold with nested non-tail local fixpoints: CRANE_CHECK_IR=1 reports "frame plan: a binder the recursion plan finds live across a call has no local in scope standing for it". *)
Module MutualStFramePlanBinder.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Record pt : Type := mkpt { px : nat; py : bool }.
Class Sz (A : Type) := { sz : A -> nat }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Class Mon (A : Type) := { munit : A; mop : A -> A -> A }.
#[global] Instance mon_nat : Mon nat := { munit := 0; mop := Nat.add }.
Definition mconcat {A : Type} `{Mon A} (l : list A) : A := fold_right mop munit l.
Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Fixpoint h4a (n50 : (list tree)) : (st (ptree nat)) :=
  match n50 with [] => (sret (@PLeaf nat)) | h63 :: r64 => (let fix go65 (l66 : (list (bool * tree))) (acc67 : (st (ptree nat))) {struct l66} : (st (ptree nat)) := match l66 with [] => (h4a r64) | e68 :: rest69 => go65 rest69 (sret (@PLeaf nat)) end in go65 (@nil (bool * tree)) (h4a r64))
  end
with h4b (n76 : (list tree)) : nat :=
  match n76 with [] => 9%nat | h77 :: r78 => (fold_left (fun (acc79 : nat) (e80 : (nat * pt)) => (mconcat (let x81 := [(mkpt 4%nat false); (mkpt 11%nat false); (mkpt 7%nat true)] in [252%nat; 8%nat; 42%nat; 5%nat]))) (let x82 := (proj1_sig (exist (fun n : nat => n = n) 6%nat eq_refl)) in (let fix go83 (l84 : (list (ptree nat))) (acc85 : (list (nat * pt))) {struct l84} : (list (nat * pt)) := match l84 with [] => acc85 | e86 :: rest87 => let rv88 := go83 rest87 acc85 in acc85 end in go83 [(@PLeaf nat); (@PLeaf nat); (@PLeaf nat); (@PLeaf nat)] [(7%nat, (mkpt 6%nat true)); (5%nat, (mkpt 0%nat true))])) (let fix go89 (l90 : (list (sum nat nat))) (acc91 : nat) {struct l90} : nat := match l90 with [] => (let fix go94 (l95 : (list bool)) (acc96 : nat) {struct l95} : nat := match l95 with [] => acc96 | e97 :: rest98 => let rv99 := go94 rest98 acc96 in rv99 end in go94 [true; true; false] acc91) | e92 :: rest93 => go89 rest93 (if true then 232%nat else acc91) end in go89 (let x100 := (fun k101 : nat => false) in [(@inr nat nat 6%nat)]) 10%nat))
  end.
End MutualStFramePlanBinder.

Crane Extraction "mutual_st_frame_plan_binder" MutualStFramePlanBinder.
