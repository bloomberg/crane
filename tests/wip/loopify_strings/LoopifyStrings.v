From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyStrings.

(* String-like operations on lists of nat (char codes) *)

(* Helper: append *)
Fixpoint append (l1 l2 : list nat) : list nat :=
  match l1 with
  | [] => l2
  | h :: t => h :: append t l2
  end.

(* Join with separator *)
Fixpoint join_with (sep : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: sep :: join_with sep xs
  end.

(* Repeat string n times *)
Fixpoint repeat_string (s : list nat) (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => append s (repeat_string s n')
  end.

(* Repeat with separator *)
Fixpoint repeat_with_sep (s sep : list nat) (n : nat) : list nat :=
  match n with
  | 0 => []
  | 1 => s
  | S n' => append s (append sep (repeat_with_sep s sep n'))
  end.

(* String chain with separator and end marker *)
Fixpoint string_chain_fuel (fuel : nat) (s : list nat) (n : nat)
                           (sep end_marker : list nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
    if n <=? 0 then []
    else append s (append sep (append (string_chain_fuel fuel' s (n - 1) sep end_marker)
                                     end_marker))
  end.

Definition string_chain (s : list nat) (n : nat) (sep end_marker : list nat) : list nat :=
  string_chain_fuel n s n sep end_marker.

(* Check if palindrome *)
Fixpoint reverse (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: xs => append (reverse xs) [x]
  end.

Fixpoint list_eq (l1 l2 : list nat) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: xs, y :: ys => (x =? y) && list_eq xs ys
  | _, _ => false
  end.

Definition is_palindrome (l : list nat) : bool :=
  list_eq l (reverse l).

(* Intersperse - insert element between all elements *)
Fixpoint intersperse (sep : nat) (l : list nat) : list nat :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: sep :: intersperse sep xs
  end.

(* Intercalate - insert list between all lists *)
Fixpoint intercalate (sep : list nat) (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | [x] => x
  | x :: xs => append x (append sep (intercalate sep xs))
  end.

(* Replicate character *)
Fixpoint replicate (n : nat) (x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: replicate n' x
  end.

(* Run length encoding *)
Fixpoint run_length_aux (current : nat) (count : nat) (l : list nat)
                        : list (nat * nat) :=
  match l with
  | [] => if count =? 0 then [] else [(current, count)]
  | x :: xs =>
    if x =? current then
      run_length_aux current (count + 1) xs
    else
      if count =? 0 then run_length_aux x 1 xs
      else (current, count) :: run_length_aux x 1 xs
  end.

Definition run_length_encode (l : list nat) : list (nat * nat) :=
  match l with
  | [] => []
  | x :: xs => run_length_aux x 1 xs
  end.

End LoopifyStrings.

Set Crane Loopify.
Crane Extraction "loopify_strings" LoopifyStrings.
