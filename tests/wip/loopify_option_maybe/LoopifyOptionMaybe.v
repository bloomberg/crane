From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyOptionMaybe.

(* Option/Maybe operations on lists *)

(* Find first element matching condition *)
Fixpoint find_even (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if (x mod 2) =? 0 then Some x else find_even xs
  end.

(* Find first element greater than threshold *)
Fixpoint find_greater (threshold : nat) (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: xs => if threshold <? x then Some x else find_greater threshold xs
  end.

(* Lookup in association list *)
Fixpoint lookup (key : nat) (l : list (nat * nat)) : option nat :=
  match l with
  | [] => None
  | (k, v) :: xs => if key =? k then Some v else lookup key xs
  end.

(* Lookup all values for key *)
Fixpoint lookup_all (key : nat) (l : list (nat * nat)) : list nat :=
  match l with
  | [] => []
  | (k, v) :: xs => if key =? k then v :: lookup_all key xs else lookup_all key xs
  end.

(* Safe head *)
Fixpoint safe_head (l : list nat) : option nat :=
  match l with
  | [] => None
  | x :: _ => Some x
  end.

(* Safe tail *)
Fixpoint safe_tail (l : list nat) : option (list nat) :=
  match l with
  | [] => None
  | _ :: xs => Some xs
  end.

(* Extract all Some values from option list *)
Fixpoint catMaybes (l : list (option nat)) : list nat :=
  match l with
  | [] => []
  | None :: xs => catMaybes xs
  | Some x :: xs => x :: catMaybes xs
  end.

(* Find index of first even number *)
Fixpoint find_index_even_aux (l : list nat) (idx : nat) : option nat :=
  match l with
  | [] => None
  | x :: xs =>
    if (x mod 2) =? 0 then Some idx
    else find_index_even_aux xs (idx + 1)
  end.

Definition find_index_even (l : list nat) : option nat :=
  find_index_even_aux l 0.

End LoopifyOptionMaybe.

Set Crane Loopify.
Crane Extraction "loopify_option_maybe" LoopifyOptionMaybe.
