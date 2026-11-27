From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.ZInt Mapping.NInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: the generated program as shrunk by ephyra (hand
    reduction lost the trigger).

    [g1] recurses on a tree; its [Node] branch calls a local fixpoint whose
    base case and initial accumulator both call [g1] on the left subtree.
    The explicit-stack frames read [acc29], declared only as a member of
    [_after_g1_in_Nil]: "use of undeclared identifier 'acc29'".  The frame
    kept the local [_x2] a pattern bound at [acc29]'s level in the branch the
    continuation ran in; it now keeps the local bound at the site the
    recursion plan names (as [loopify_rematch_frame_binder]). *)
Module FrameBinderLocalFixAcc.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Record pt : Type := mkpt { px : nat; py : bool }.
Fixpoint tree_obs (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r => (tree_obs l * 7 + v + tree_obs r * 3) mod 10007
  end.
Fixpoint tins (n : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf n Leaf
  | Node l v r => if Nat.ltb n v then Node (tins n l) v r else Node l v (tins n r)
  end.
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.
#[global] Instance sz_bool : Sz bool := { sz b := if b then 1 else 0 }.
#[global] Instance sz_tree : Sz tree := { sz := tree_obs }.
#[global] Instance sz_list {A : Type} `{Sz A} : Sz (list A) :=
  { sz l := fold_left (fun a x => (a + sz x) mod 10007) l 0 }.
#[global] Instance sz_pair {A B : Type} `{Sz A} `{Sz B} : Sz (A * B) :=
  { sz p := (sz (fst p) * 3 + sz (snd p)) mod 10007 }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Arguments PLeaf {A}.
Arguments PNode {A} _ _ _.
Fixpoint pmap {A B : Type} (f : A -> B) (t : ptree A) : ptree B :=
  match t with PLeaf => PLeaf | PNode l x r => PNode (pmap f l) (f x) (pmap f r) end.
Fixpoint pfold {A B : Type} (f : B -> A -> B) (t : ptree A) (acc : B) : B :=
  match t with PLeaf => acc | PNode l x r => pfold f r (f (pfold f l acc) x) end.
Fixpoint psize {A : Type} (t : ptree A) : nat :=
  match t with PLeaf => 0 | PNode l _ r => S (psize l + psize r) end.
CoInductive stream : Type := SCons : nat -> stream -> stream.
CoFixpoint sconst (n : nat) : stream := SCons n (sconst n).
CoFixpoint sfrom (n : nat) : stream := SCons n (sfrom (S n)).
CoFixpoint smap (f : nat -> nat) (s : stream) : stream :=
  match s with SCons x r => SCons (f x) (smap f r) end.
Fixpoint stake (k : nat) (s : stream) : list nat :=
  match k with O => [] | S k' => match s with SCons x r => x :: stake k' r end end.
Definition shd (s : stream) : nat := match s with SCons x _ => x end.
Definition stl (s : stream) : stream := match s with SCons _ r => r end.

Fixpoint g1 (t3 : tree) (a1 : bool) (a2 : Z) : Z :=
  match t3 with Leaf => 0%Z | Node tl4 tv5 tr6 => (let fix go27 (l28 : (list nat)) (acc29 : Z) {struct l28} : Z := match l28 with [] => (Z.min (g1 tl4 true 0%Z) acc29) | e30 :: rest31 => 0%Z end in go27 (@nil nat) (match a2 with Z0 => 0%Z | Zpos _ => 0%Z | Zneg _ => (g1 tl4 true 0%Z) end))
  end.

Definition t_1 : nat :=
  0%nat.

End FrameBinderLocalFixAcc.

Crane Extraction "frame_binder_local_fix_acc" FrameBinderLocalFixAcc.
