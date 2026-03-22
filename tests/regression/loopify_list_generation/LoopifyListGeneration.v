From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListGeneration.

(* List generation and replication functions *)

(* Replicate - repeat element n times *)
Fixpoint replicate (n : nat) (x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: replicate n' x
  end.

(* Stutter - duplicate each element *)
Fixpoint stutter (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => x :: x :: stutter xs
  end.

(* Cycle - repeat list n times *)
Fixpoint cycle (n : nat) (l : list nat) : list nat :=
  match n with
  | 0 => []
  | S n' => app l (cycle n' l)
  end.

(* Iterate - apply function n times and collect results *)
Fixpoint iterate (n : nat) (x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: iterate n' (x + 1)
  end.

(* Replicate list - replicate elements based on counts *)
Fixpoint replicate_list (l : list (nat * nat)) : list nat :=
  match l with
  | [] => []
  | (n, x) :: rest =>
    let rep := replicate n x in
    app rep (replicate_list rest)
  end.

(* Repeat with separator *)
Fixpoint repeat_with_sep (sep : nat) (n : nat) (x : nat) : list nat :=
  match n with
  | 0 => []
  | S 0 => [x]
  | S n' => x :: sep :: repeat_with_sep sep n' x
  end.

(* Build list from range *)
Fixpoint range (start : nat) (len : nat) : list nat :=
  match len with
  | 0 => []
  | S len' => start :: range (start + 1) len'
  end.

End LoopifyListGeneration.

Set Crane Loopify.
Crane Extraction "loopify_list_generation" LoopifyListGeneration.
