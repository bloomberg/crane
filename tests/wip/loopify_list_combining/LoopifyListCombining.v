From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListCombining.

(* List combining and interleaving operations *)

(* Helper: append *)
Fixpoint append (a b : list nat) : list nat :=
  match a with
  | [] => b
  | h :: t => h :: append t b
  end.

(* Intersperse - insert separator between elements *)
Fixpoint intersperse (sep : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: sep :: intersperse sep xs
  end.

(* Intercalate - intersperse and concatenate *)
Fixpoint intercalate (sep : list nat) (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | [x] => x
  | x :: xs => append x (append sep (intercalate sep xs))
  end.

(* Concat - flatten list of lists *)
Fixpoint concat (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | x :: xs => append x (concat xs)
  end.

(* Mapcat - map and concatenate *)
Fixpoint mapcat (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => append [x; x] (mapcat xs)
  end.

(* Interleave two lists *)
Fixpoint interleave_two (l1 l2 : list nat) : list nat :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | x :: xs, y :: ys => x :: y :: interleave_two xs ys
  end.

(* Concat with separator *)
Fixpoint concat_sep (sep : nat) (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | [x] => x
  | x :: xs => append x (sep :: concat_sep sep xs)
  end.

End LoopifyListCombining.

Set Crane Loopify.
Crane Extraction "loopify_list_combining" LoopifyListCombining.
