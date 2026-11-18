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

    [t_1] computes 0 through [mconcat] of a match on a local fixpoint; the C++ initialiser of [t_1] reads [f4], a constant [0] defined after it in the same file (static initialisation order), and CRANE_CHECK_IR=1 reports "value order: the value t_1 reads f4, written after it".

    [t_1] reads no [f4]: it names [tree] as a type, and the check followed
    a struct to everything its methods read, [g6]'s [f4] included.  A method
    is now a function of its own to the check, by its global. *)
Module ValueOrderLaterConstant.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Class Sz (A : Type) := { sz : A -> nat }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
CoInductive stream : Type := SCons : nat -> stream -> stream.
Class Mon (A : Type) := { munit : A; mop : A -> A -> A }.
#[global] Instance mon_list {A : Type} : Mon (list A) := { munit := []; mop := @app A }.
Definition mconcat {A : Type} `{Mon A} (l : list A) : A := fold_right mop munit l.

Definition t_1 : nat :=
  ((fun w36 : (list nat) => fold_left (fun w38 e => (w38 * 3 + (fun w37 : nat => w37) e) mod 10007) w36 1) (mconcat (match (let fix go9 (l10 : (list (list tree))) (acc11 : bool) {struct l10} : bool := match l10 with [] => true | e12 :: rest13 => let rv15 := go9 rest13 acc11 in rv15 end in go9 (@nil (list tree)) true) with true => (@nil (list nat)) | false => (@nil (list nat)) end))).

Definition f4 : nat :=
  0%nat.

Fixpoint g6 (t68 : tree) (a66 : nat) (a67 : bool) : tree :=
  (Node Leaf f4 Leaf).
End ValueOrderLaterConstant.

Crane Extraction "value_order_later_constant" ValueOrderLaterConstant.
