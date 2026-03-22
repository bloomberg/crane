From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListWindows.

(* List windowing and chunking operations *)

(* Helper: list length *)
Fixpoint len (l : list nat) : nat :=
  match l with
  | [] => 0
  | _ :: xs => 1 + len xs
  end.

(* Helper: map cons onto each list *)
Fixpoint map_cons_helper (x : nat) (ll : list (list nat)) : list (list nat) :=
  match ll with
  | [] => []
  | r :: rs => (x :: r) :: map_cons_helper x rs
  end.

(* Helper: drop first n elements *)
Fixpoint drop (m : nat) (xs : list nat) : list nat :=
  match m with
  | 0 => xs
  | S m' =>
    match xs with
    | [] => []
    | _ :: ys => drop m' ys
    end
  end.

(* Helper: span equal elements *)
Fixpoint span_eq (first : nat) (lst : list nat) : list nat * list nat :=
  match lst with
  | [] => ([], [])
  | y :: ys =>
    if first =? y then
      let '(s, r) := span_eq first ys in
      (y :: s, r)
    else
      ([], lst)
  end.

(* Differences between adjacent elements *)
Fixpoint differences (l : list nat) : list nat :=
  match l with
  | [] => []
  | [_] => []
  | x :: xs =>
    match xs with
    | [] => []
    | y :: rest => (y - x) :: differences xs
    end
  end.

(* Sliding pairs *)
Fixpoint sliding_pairs (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | [_] => []
  | a :: xs =>
    match xs with
    | [] => []
    | b :: _ => (a, b) :: sliding_pairs xs
    end
  end.

(* Inits - all prefixes *)
Fixpoint inits (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | x :: xs => [] :: map_cons_helper x (inits xs)
  end.

(* Tails - all suffixes *)
Fixpoint tails (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | _ :: xs => l :: tails xs
  end.

(* Take first n elements *)
Fixpoint take (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => []
  | S n' =>
    match l with
    | [] => []
    | x :: xs => x :: take n' xs
    end
  end.

(* Windows of size n *)
Fixpoint windows_fuel (fuel : nat) (n : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | _ :: xs =>
      if len l <? n then []
      else take n l :: windows_fuel fuel' n xs
    end
  end.

Definition windows (n : nat) (l : list nat) : list (list nat) :=
  windows_fuel (len l) n l.

(* Chunks of size n *)
Fixpoint chunks_fuel (fuel : nat) (n : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | _ =>
      let chunk := take n l in
      let rest := drop n l in
      chunk :: chunks_fuel fuel' n rest
    end
  end.

Definition chunks (n : nat) (l : list nat) : list (list nat) :=
  chunks_fuel (len l) n l.

(* Group consecutive equal elements *)
Fixpoint group_fuel (fuel : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match l with
    | [] => []
    | x :: xs =>
      let '(same, rest) := span_eq x xs in
      (x :: same) :: group_fuel fuel' rest
    end
  end.

Definition group (l : list nat) : list (list nat) :=
  group_fuel (len l) l.

End LoopifyListWindows.

Set Crane Loopify.
Crane Extraction "loopify_list_windows" LoopifyListWindows.
