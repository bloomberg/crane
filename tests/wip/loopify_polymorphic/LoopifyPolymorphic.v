From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyPolymorphic.

(* Polymorphic list operations that work on any type *)

(* Polymorphic length *)
Fixpoint poly_length {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0
  | _ :: xs => 1 + poly_length xs
  end.

(* Polymorphic reverse *)
Fixpoint poly_reverse {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => poly_reverse xs ++ [x]
  end.

(* Polymorphic append *)
Fixpoint poly_append {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: xs => x :: poly_append xs l2
  end.

(* Polymorphic last element *)
Fixpoint poly_last {A : Type} (l : list A) : option A :=
  match l with
  | [] => None
  | [x] => Some x
  | _ :: xs => poly_last xs
  end.

(* Polymorphic take *)
Fixpoint poly_take {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => []
  | S n' =>
    match l with
    | [] => []
    | x :: xs => x :: poly_take n' xs
    end
  end.

(* Polymorphic drop *)
Fixpoint poly_drop {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => l
  | S n' =>
    match l with
    | [] => []
    | _ :: xs => poly_drop n' xs
    end
  end.

(* Polymorphic nth element *)
Fixpoint poly_nth {A : Type} (n : nat) (l : list A) : option A :=
  match l with
  | [] => None
  | x :: xs => if n =? 0 then Some x else poly_nth (n - 1) xs
  end.

(* Polymorphic filter *)
Fixpoint poly_filter {A : Type} (p : A -> bool) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if p x then x :: poly_filter p xs else poly_filter p xs
  end.

(* Polymorphic map *)
Fixpoint poly_map {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => f x :: poly_map f xs
  end.

(* Polymorphic zip *)
Fixpoint poly_zip {A B : Type} (l1 : list A) (l2 : list B) : list (A * B) :=
  match l1, l2 with
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => (x, y) :: poly_zip xs ys
  end.

(* Polymorphic unzip *)
Fixpoint poly_unzip {A B : Type} (l : list (A * B)) : list A * list B :=
  match l with
  | [] => ([], [])
  | (a, b) :: rest =>
    let '(as_, bs) := poly_unzip rest in
    (a :: as_, b :: bs)
  end.

(* Polymorphic partition *)
Fixpoint poly_partition {A : Type} (p : A -> bool) (l : list A) : list A * list A :=
  match l with
  | [] => ([], [])
  | x :: xs =>
    let '(trues, falses) := poly_partition p xs in
    if p x then (x :: trues, falses)
    else (trues, x :: falses)
  end.

(* Polymorphic member check *)
Fixpoint poly_member {A : Type} (eq : A -> A -> bool) (x : A) (l : list A) : bool :=
  match l with
  | [] => false
  | y :: ys => if eq x y then true else poly_member eq x ys
  end.

(* Polymorphic replicate *)
Fixpoint poly_replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | 0 => []
  | S n' => x :: poly_replicate n' x
  end.

(* Instantiate with nat for testing *)
Definition nat_length : list nat -> nat := @poly_length nat.
Definition nat_reverse : list nat -> list nat := @poly_reverse nat.
Definition nat_append : list nat -> list nat -> list nat := @poly_append nat.
Definition nat_last : list nat -> option nat := @poly_last nat.
Definition nat_take : nat -> list nat -> list nat := @poly_take nat.
Definition nat_drop : nat -> list nat -> list nat := @poly_drop nat.
Definition nat_nth : nat -> list nat -> option nat := @poly_nth nat.

Definition nat_eq (x y : nat) : bool := x =? y.
Definition is_even (x : nat) : bool := x mod 2 =? 0.

Definition nat_filter : (nat -> bool) -> list nat -> list nat := @poly_filter nat.
Definition nat_map : (nat -> nat) -> list nat -> list nat := @poly_map nat nat.
Definition nat_partition : (nat -> bool) -> list nat -> list nat * list nat := @poly_partition nat.
Definition nat_member : nat -> list nat -> bool := poly_member nat_eq.
Definition nat_replicate : nat -> nat -> list nat := @poly_replicate nat.

End LoopifyPolymorphic.

Set Crane Loopify.
Crane Extraction "loopify_polymorphic" LoopifyPolymorphic.
