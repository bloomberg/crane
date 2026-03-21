From Stdlib Require Import List.
From Stdlib Require Import Nat.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

Module LoopifyListOfLists.

(* Operations on nested lists *)

(* Intercalate - insert separator between lists *)
Fixpoint intercalate (sep : list nat) (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | [x] => x
  | x :: xs => app x (app sep (intercalate sep xs))
  end.

(* Transpose - swap rows and columns *)
Fixpoint map_hd (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | [] :: rest => map_hd rest
  | (h :: _) :: rest => h :: map_hd rest
  end.

Fixpoint map_tl (ll : list (list nat)) : list (list nat) :=
  match ll with
  | [] => []
  | [] :: rest => map_tl rest
  | (_ :: t) :: rest => t :: map_tl rest
  end.

Fixpoint all_empty (ll : list (list nat)) : bool :=
  match ll with
  | [] => true
  | [] :: rest => all_empty rest
  | (_ :: _) :: _ => false
  end.

Fixpoint transpose_fuel (fuel : nat) (ll : list (list nat)) : list (list nat) :=
  match fuel with
  | 0 => []
  | S fuel' =>
    match ll with
    | [] => []
    | [] :: _ => []
    | rows =>
      if all_empty rows then []
      else
        let heads := map_hd rows in
        let tails := map_tl rows in
        heads :: transpose_fuel fuel' tails
    end
  end.

(* Length of a single list *)
Fixpoint list_len (l : list nat) : nat :=
  match l with
  | [] => 0
  | _ :: xs => 1 + list_len xs
  end.

Fixpoint total_length (ll : list (list nat)) : nat :=
  match ll with
  | [] => 0
  | l :: rest => list_len l + total_length rest
  end.

Definition transpose (ll : list (list nat)) : list (list nat) :=
  transpose_fuel (total_length ll) ll.

(* Flatten - concatenate all sublists *)
Fixpoint flatten (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | l :: rest => app l (flatten rest)
  end.

(* Count total elements *)
Fixpoint count_total (ll : list (list nat)) : nat :=
  match ll with
  | [] => 0
  | l :: rest => list_len l + count_total rest
  end.

(* Get first element of each sublist *)
Fixpoint firsts (ll : list (list nat)) : list nat :=
  match ll with
  | [] => []
  | [] :: rest => firsts rest
  | (h :: _) :: rest => h :: firsts rest
  end.

(* Check if all sublists are empty *)
Fixpoint all_nil (ll : list (list nat)) : bool :=
  match ll with
  | [] => true
  | [] :: rest => all_nil rest
  | (_ :: _) :: _ => false
  end.

(* Zip two lists of lists *)
Fixpoint zip_lists (ll1 ll2 : list (list nat)) : list (list nat * list nat) :=
  match ll1, ll2 with
  | [], _ => []
  | _, [] => []
  | l1 :: rest1, l2 :: rest2 => (l1, l2) :: zip_lists rest1 rest2
  end.

(* Maximum length among all sublists *)
Fixpoint max_length (ll : list (list nat)) : nat :=
  match ll with
  | [] => 0
  | l :: rest => max (list_len l) (max_length rest)
  end.

End LoopifyListOfLists.

Set Crane Loopify.
Crane Extraction "loopify_list_of_lists" LoopifyListOfLists.
