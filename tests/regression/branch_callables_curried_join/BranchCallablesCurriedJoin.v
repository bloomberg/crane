From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith.
Import ListNotations.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Match branches producing two-argument function values, one a curried
    lambda, the other a composed let-lambda ([let cf .. in let cg .. in fun c
    => cf (cg c)]), bound by a beta-redex: the C++ declares the variable at
    one branch's type and assigns the other ("no viable overloaded '='").
    Remaining after d7cf5aaae (common crane::fn type for joined callables).
    A match's branches now carry the slot into their tails, so the lambda
    knows the Core type backing the two-parameter function it is written
    against, and takes the parameter its body leaves to a partial
    application. *)
Module BranchCallablesCurriedJoin.

Record pt : Type := mkpt { px : nat; py : bool }.

Inductive tree : Type := Leaf : tree | Node : tree -> nat -> tree -> tree.
Fixpoint tins (n : nat) (t : tree) : tree :=
  match t with
  | Leaf => Node Leaf n Leaf
  | Node l v r => if Nat.ltb n v then Node (tins n l) v r else Node l v (tins n r)
  end.
Fixpoint tree_obs (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l v r => Nat.modulo (tree_obs l * 7 + v + tree_obs r * 3) 10007
  end.
Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_nat : Sz nat := { sz n := n }.
#[global] Instance sz_bool : Sz bool := { sz b := if b then 1 else 0 }.
#[global] Instance sz_tree : Sz tree := { sz := tree_obs }.
#[global] Instance sz_list {A : Type} `{Sz A} : Sz (list A) :=
  { sz l := fold_left (fun a x => Nat.modulo (a + sz x) 10007) l 0 }.
Inductive ptree (A : Type) : Type := PLeaf : ptree A | PNode : ptree A -> A -> ptree A -> ptree A.
Arguments PLeaf {A}.
Arguments PNode {A} _ _ _.


Definition t (l : list nat) : nat :=
  (fun w : nat -> pt -> bool => if w 0 (mkpt 0 true) then 1 else 2)
  (match List.length l with
   | O => (fun _ : nat => (fun _ : pt => true))
   | S _ => (let cf := (fun _ : bool => (fun _ : pt => false)) in
             let cg := (fun _ : nat => true) in fun c : nat => cf (cg c))
   end).

(** The same join as a [fold_left] step's result: the accumulator passes
    through [fold_left]'s type variable, so the step returns its curried
    spelling, and so do both branches. *)
Definition t2 (l : list nat) : nat :=
  (fold_left (fun (acc : Z -> bool -> nat) (x : nat) =>
     match x with
     | O => (fun _ : Z => (fun b : bool => if b then 1 else 0))
     | S _ => (let cf := (fun (n : nat) (_ : bool) => n) in fun z : Z => cf (acc z false))
     end) l (fun _ _ => 7)) 3%Z true.

(** Round-8 variants: the join at list types; a class method as a curried
    result; a callable inside a pair; a let-wrapped composition passed for
    a local fixpoint's function parameter. *)
Definition v1 : nat :=
  (fun w : list nat -> nat -> nat => w [1] 2)
  (match (sz (@nil tree)) with
   | O => (fun _ : list nat => fun _ : nat => 0)
   | S _ => (let cf := (fun _ : list tree => fun _ : nat => 0) in
             let cg := (fun _ : list nat => [Leaf]) in fun c : list nat => cf (cg c))
   end).

Definition v2 : nat :=
  (fun w : list nat -> nat -> nat => w [1] 2)
  (match (sz (@nil tree)) with
   | O => (fun y : list nat => match y with [] => sz | _ :: _ => (fun _ : nat => 0) end)
   | S _ => (let cf := (fun _ : list tree => fun _ : nat => 0) in
             let cg := (fun _ : list nat => [Leaf]) in fun c : list nat => cf (cg c))
   end).

Definition v3 (x : option nat) : nat :=
  let p := match (match x with Some o => tins o Leaf | None => Leaf end) with
           | Leaf => (0, fun _ : nat => 0)
           | Node _ v _ => (v, let fix go (l : list nat) (acc : nat -> nat) := match l with [] => acc | _ :: r => go r acc end in go [] (fun _ => 0))
           end in
  fst p + snd p 1.

Definition f1 (a : ptree (nat * nat)) : nat -> tree -> nat :=
  let fix go (l : list bool) (acc : nat -> tree -> nat) := match l with [] => (fun _ _ => 0) | _ :: r => go r (fun _ _ => 0) end in
  go [] (let cf := (fun _ : tree => fun _ : tree => 0) in let cg := (fun _ : nat => Leaf) in fun c : nat => cf (cg c)).

Definition v4 : nat := f1 PLeaf 3 Leaf.

End BranchCallablesCurriedJoin.

Crane Extraction "branch_callables_curried_join" BranchCallablesCurriedJoin.
