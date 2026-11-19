From Crane Require Import Mapping.NatIntStd Mapping.ZInt.
From Crane Require Extraction.
From Stdlib Require Import List ZArith Strings.String.
Import ListNotations.
Open Scope string_scope.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: generated programs, shrunk by ephyra and reduced by
    hand.

    A function type behind a definition ([st A := nat -> A * nat]) was
    spelled two ways: unfolded, a function of the arrows it hides, at some
    sites, and kept, [st<A>], at others.  Where the two met the C++ did not
    compile: a parameter typed [nat * nat -> st Z] passed on from a match
    ("no viable conversion from 'const fn<st<int64_t> (pair)>' to
    'fn<pair<int64_t,uint64_t> (pair, uint64_t)>'"), a composed let-lambda
    returning [st bool], and a local fixpoint over [list (st bool)]. *)
Module FunctionAliasSpelling.

Inductive tree : Type := Leaf | Node (l : tree) (v : nat) (r : tree).

Definition st (A : Type) : Type := nat -> A * nat.
Definition sret {A : Type} (a : A) : st A := fun s => (a, s).

Fixpoint g2 (t : tree) (a : nat * nat -> st Z) : tree :=
  match t with
  | Leaf => Leaf
  | Node l v _ => g2 l (match v with O => a | S _ => (fun _ => sret 0%Z) end)
  end.

(** [g2] with its parameter observed at the leaf. *)
Fixpoint g2z (t : tree) (a : nat * nat -> st Z) : Z :=
  match t with
  | Leaf => fst (a (0, 0) 0)
  | Node l v _ => g2z l (match v with O => a | S _ => (fun _ => sret 0%Z) end)
  end.

Definition t1 : tree := g2 (Node (Node Leaf 1 Leaf) 0 Leaf) (fun _ => sret 5%Z).
Definition t1_leaf : bool := match t1 with Leaf => true | _ => false end.
Definition z1 : Z := g2z (Node Leaf 0 Leaf) (fun _ => sret 5%Z).
Definition z2 : Z := g2z (Node (Node Leaf 0 Leaf) 1 Leaf) (fun _ => sret 5%Z).

Definition sf2 (a6 : st bool) : list nat -> st bool :=
  let cf := (fun _ : nat * string => a6) in
  let cg := (fun _ : list nat => (0, "")) in
  fun c => cf (cg c).

Definition b2 : bool := fst (sf2 (sret true) [1; 2] 0).
Definition n2 : nat := snd (sf2 (sret false) [] 4).

Definition f3 : option bool :=
  let fix go (l : list (st bool)) (acc : option bool) {struct l} : option bool :=
    match l with
    | [] => acc
    | x :: r => go r (Some (fst (x 0)))
    end in
  go [sret true; sret true] None.

End FunctionAliasSpelling.

Crane Extraction "function_alias_spelling" FunctionAliasSpelling.
