From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
From Stdlib Require Import List ZArith NArith Ascii Strings.String.
Import ListNotations.
Local Open Scope nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity).
Infix "/" := Nat.div.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: the generated program as shrunk by ephyra (hand
    reduction lost the trigger).

    In functor [F4], [h] returns a function through a local fixpoint whose
    accumulator step matches on a match of a [Z] parameter, with a branch
    matching a list literal.  Under CRANE_CHECK_IR=1 (the test suite's
    setting) extraction fails the Core check: "binder scopes: the variable at
    index 3 is x0_0 to the names in scope and _x to the binders typed in
    scope". *)
Module FunctorBinderScopeCheck.

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

Definition t_1 : nat :=
  0%nat.

Module Type SIG4.
  Parameter t : Type.
  Parameter d : t.
  Parameter op : t -> t -> t.
End SIG4.

Module F4 (E : SIG4).
Definition h (a128 : E.t) (a129 : Z) : (nat -> E.t) :=
  (let fix go130 (l131 : (list (list nat))) (acc132 : (nat -> E.t)) {struct l131} : (nat -> E.t) := match l131 with [] => acc132 | e133 :: rest134 => go130 rest134 (match (match a129 with Z0 => false | Zpos _ => true | Zneg _ => true end) with true => (match [(@nil nat); (@nil nat); (@nil nat); (@nil nat)] with [] => acc132 | [h136] => acc132 | h136 :: h138 :: r137 => (fun k139 : nat => E.d) end) | false => (fun y140 : nat => a128) end) end in go130 (@nil (list nat)) (fun y143 : nat => E.d)).
End F4.
Module M4_1 <: SIG4.
  Definition t : Type := Z.
  Definition d : t := 15%Z.
  Definition op (u144 v145 : t) : t := (match (let x146 : (ptree bool) := (PNode (@PLeaf bool) true (@PLeaf bool)) in 10%nat) with O => (Z.sgn v145) | S m147 => (Z.max v145 (-5)%Z) end).
End M4_1.
Module A4_1 := F4 M4_1.


End FunctorBinderScopeCheck.

Crane Extraction "functor_binder_scope_check" FunctorBinderScopeCheck.
