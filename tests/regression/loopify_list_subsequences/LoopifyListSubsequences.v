From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListSubsequences.

(* List subsequence operations *)

Fixpoint map_cons_helper (x : nat) (ll : list (list nat)) : list (list nat) :=
  match ll with
  | [] => []
  | t :: ts => (x :: t) :: map_cons_helper x ts
  end.

(* Tails - all suffixes of list *)
Fixpoint tails (l : list nat) : list (list nat) :=
  match l with
  | [] => [[]]
  | _ :: xs => l :: tails xs
  end.

(* Inits - all prefixes of list *)
Fixpoint inits_fuel (fuel : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | 0 => [[]]
  | S fuel' =>
    match l with
    | [] => [[]]
    | x :: xs =>
      let rest := inits_fuel fuel' xs in
      [] :: map_cons_helper x rest
    end
  end.

Definition inits (l : list nat) : list (list nat) :=
  inits_fuel (length l) l.

(* Init - all but last element *)
Fixpoint init_list (l : list nat) : list nat :=
  match l with
  | [] => []
  | [_] => []
  | x :: xs => x :: init_list xs
  end.

(* Snoc - append element to end *)
Fixpoint snoc (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => h :: snoc t x
  end.

(* Last - get last element *)
Fixpoint last_elem (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | _ :: xs => last_elem xs
  end.

(* Nth - get nth element *)
Fixpoint nth_elem (n : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => if n =? 0 then x else nth_elem (n - 1) xs
  end.

(* Split at position n *)
Fixpoint split_at (n : nat) (l : list nat) : list nat * list nat :=
  match n with
  | 0 => ([], l)
  | S n' =>
    match l with
    | [] => ([], [])
    | x :: xs =>
      let '(before, after) := split_at n' xs in
      (x :: before, after)
    end
  end.

End LoopifyListSubsequences.

Set Crane Loopify.
Crane Extraction "loopify_list_subsequences" LoopifyListSubsequences.
