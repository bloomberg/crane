(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* From CertiCoq benchmarks, with its MIT license. *)
From Stdlib Require Import Nat Lists.List.

Module Priqueue.

Import ListNotations.
Import Nat.
Definition key := nat.

Inductive tree : Type :=
| Node : key -> tree -> tree -> tree
| Leaf : tree.

Definition priqueue : Type := list tree.

Definition empty : priqueue := nil.

Notation "a >? b" := (ltb b a) (at level 70, only parsing) : nat_scope.

Definition smash (t u : tree) : tree :=
  match t , u with
  | Node x t1 Leaf, Node y u1 Leaf =>
      if x >? y
        then Node x (Node y u1 t1) Leaf
        else Node y (Node x t1 u1) Leaf
  | _ , _ => Leaf (* arbitrary bogus tree *)
  end.

Fixpoint carry (q : list tree) (t : tree) : list tree :=
  match q, t with
  | nil, Leaf     => nil
  | nil, _        => t :: nil
  | Leaf :: q', _ => t :: q'
  | u :: q', Leaf => u :: q'
  | u :: q', _    => Leaf :: carry q' (smash t u)
 end.

Definition insert (x : key) (q : priqueue) : priqueue :=
  carry q (Node x Leaf Leaf).

Fixpoint join (p q : priqueue) (c : tree) : priqueue :=
  match p, q, c with
  | [], _ , _ => carry q c
  | _, [], _  => carry p c
  | Leaf :: p', Leaf::q', _ => c :: join p' q' Leaf
  | Leaf :: p', q1 :: q', Leaf => q1 :: join p' q' Leaf
  | Leaf :: p', q1 :: q', Node _ _ _  => Leaf :: join p' q' (smash c q1)
  | p1 :: p', Leaf :: q', Leaf => p1 :: join p' q' Leaf
  | p1 :: p', Leaf :: q', Node _ _ _   => Leaf :: join p' q' (smash c p1)
  | p1 :: p', q1 :: q', _ => c :: join p' q' (smash p1 q1)
  end.

Fixpoint unzip (t : tree) (cont : priqueue -> priqueue) : priqueue :=
  match t with
  | Node x t1 t2   =>
    let f q := Node x t1 Leaf  :: cont q in
    unzip t2 f
  | Leaf => cont nil
  end.

Definition heap_delete_max (t: tree) : priqueue :=
  match t with
  | Node x t1 Leaf => unzip t1 (fun u => u)
  | _ => nil (* bogus value for ill-formed or empty trees *)
  end.

Fixpoint find_max_helper (current : key) (q : priqueue) : key :=
  match q with
  | [] => current
  | Leaf :: q' => find_max_helper current q'
  | Node x _ _ :: q' => find_max_helper (if x >? current then x else current) q'
  end.

Fixpoint find_max (q : priqueue) : option key :=
  match q with
  | [] => None
  | Leaf :: q' => find_max q'
  | Node x _ _ :: q' => Some (find_max_helper x q')
 end.

Fixpoint delete_max_aux (m : key) (p : priqueue) : priqueue * priqueue :=
  match p with
  | Leaf :: p' => let (j,k) := delete_max_aux m p' in (Leaf::j, k)
  | Node x t1 Leaf :: p' =>
      if m >? x
      then (let (j,k) := delete_max_aux m p'
            in (Node x t1 Leaf :: j, k))
      else (Leaf :: p', heap_delete_max (Node x t1 Leaf))
  | _ => (nil, nil) (* Bogus value *)
  end.

Definition delete_max (q : priqueue) : option (key * priqueue) :=
  match find_max q with
  | None => None
  | Some m => let (p',q') := delete_max_aux m q
              in Some (m, join p' q' Leaf)
  end.

Definition merge (p q : priqueue) : priqueue := join p q Leaf.

Fixpoint insert_list (l : list nat) (q : priqueue) : priqueue :=
  match l with
  | [] => q
  | x :: l => insert_list l (insert x q)
  end.

Fixpoint make_list (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => 0 :: l
  | S 0 => 1 :: l
  | S (S n) => make_list n (S (S n) :: l)
  end.

Definition help (c : priqueue) : key :=
  match delete_max c with
  | Some (k, _) => k
  | None => 0
  end.

Definition example1 := help (merge (insert 5 (insert 3 (insert 7 nil))) (insert 3 (insert 6 (insert 9 nil)))).

Definition example2 := help (merge (insert_list (make_list 10 []) nil) (insert_list (make_list 11 []) nil)).

(*
Definition example1 : key :=
  let a := insert 5 (insert 3 (insert 7 empty)) in
  let b := insert 3 (insert 6 (insert 9 empty)) in
  let c := merge a b in
  help c.

Definition example2 : key :=
  let a := insert_list (make_list 2000 []) empty in
  let b := insert_list (make_list 2001 []) empty in
  let c := merge a b in
  help c.

*)

End Priqueue.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatIntStd.

Crane Extraction "binom" Priqueue.
