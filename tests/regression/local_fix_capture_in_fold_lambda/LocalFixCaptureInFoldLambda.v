From Crane Require Import Mapping.NatInt Mapping.NInt Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import List NArith ZArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    A local fixpoint inside a [fold_right] step lambda reads the enclosing
    function's parameter [t6]; the generated C++ reads [t6] where it is not
    declared ("use of undeclared identifier 't6'").  With the parameter also
    matched on ([g3]), CRANE_CHECK_IR=1 reports "moved value read: in g3, t6 is
    read after it is moved".  Fragile: the unrelated declarations kept from the
    generated prelude (class, ptree, stream) are needed to trigger it.
    [g5] is a smaller repro: [flat_map], and a match on the parameter as the
    local fixpoint's argument; [g6] the same in a [fold_left] lambda; [g7]
    matches on the parameter inside the local fixpoint's step; [g8] passes
    it as the local fixpoint's argument under [tree_obs].  Each function is a method of [tree], its
    parameter the receiver, read as [*this].  A stored lambda reading the
    receiver takes a copy of it, but the check for one did not look into the
    lambdas nested in it, here the local fixpoint's invoked one: the stored
    lambda kept [this] and took [t6], a name no longer bound, by move. *)
Module LocalFixCaptureInFoldLambda.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Fixpoint tree_obs (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r => Nat.modulo (tree_obs l * 7 + v + tree_obs r * 3) 10007
  end.
Fixpoint tins (n : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf n Leaf
  | Node l v r => if Nat.ltb n v then Node (tins n l) v r else Node l v (tins n r)
  end.
Record pt : Type := mkpt { px : nat; py : bool }.
Class Sz (A : Type) := { sz : A -> nat }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Arguments PLeaf {A}.
Arguments PNode {A} _ _ _.
CoInductive stream : Type := SCons : nat -> stream -> stream.

Fixpoint g2 (t6 : tree) (a4 : option nat) (a5 : nat) : tree :=
  fold_right (fun (e11 : list nat) (acc10 : tree) =>
    tins 0 (let fix go12 (l13 : list (list nat)) (acc14 : tree) {struct l13} : tree :=
              match l13 with [] => t6 | e15 :: rest16 => Leaf end in go12 [] t6)) Leaf [].

Fixpoint g3 (t6 : tree) (a4 : option nat) (a5 : nat) : tree :=
  match t6 with
  | Leaf => fold_right (fun (e11 : list nat) (acc10 : tree) =>
      tins 0 (let fix go12 (l13 : list (list nat)) (acc14 : tree) {struct l13} : tree :=
                match l13 with [] => t6 | e15 :: rest16 => Leaf end in go12 [] t6)) Leaf []
  | Node tl7 tv8 tr9 => Node (g3 tl7 None 0) 0 (g3 tr9 None 0)
  end.

Fixpoint g5 (t48 : tree) : list (option nat) :=
  flat_map (fun _ : nat =>
    let fix go (l : list N) (acc : list (option nat)) {struct l} : list (option nat) :=
      match l with [] => [] | _ :: _ => acc end in
    go (match t48 with Leaf => [] | Node _ _ _ => [] end) []) (@nil nat).

Fixpoint g6 (t : tree) : nat :=
  fold_left (fun (acc : nat) (_ : nat) =>
    let fix go (l : list nat) (a : nat) {struct l} : nat :=
      match l with [] => a + 1 | _ :: _ => 0 end in
    go (match t with Leaf => [] | Node _ _ _ => [] end) acc) [0; 0] 0.

Fixpoint g7 (t18 : tree) : nat :=
  fold_right (fun (e : nat) (acc : nat) =>
    let fix go (l : list nat) (a : nat) {struct l} : nat :=
      match l with
      | [] => a
      | x :: r => go r (match t18 with Leaf => x + a | Node _ v _ => v + a end)
      end in
    go [e; e] acc) 0 [1; 2].

Fixpoint g8 (t10 : tree) (a8 : nat) (a9 : Z) : nat :=
  fold_right (fun (e : nat) (acc : nat) =>
    tree_obs (let fix go (l : list pt) (acc2 : tree) :=
                match l with [] => Leaf | _ :: _ => t10 end in go [] t10)) 0 [].

End LocalFixCaptureInFoldLambda.

Crane Extraction "local_fix_capture_in_fold_lambda" LocalFixCaptureInFoldLambda.
