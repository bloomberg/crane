(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Non-escaping let-fix generates auto (Y-combinator), not std::function.
   Exercises both standalone and loopified-outer-function cases. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixNoStdfun.

(* Case 1: Simple non-escaping let-fix with list param *)
Definition sum_list (l : list nat) : nat :=
  let fix go (xs : list nat) (acc : nat) : nat :=
    match xs with
    | [] => acc
    | x :: rest => go rest (acc + x)
    end
  in go l 0.

(* Case 2: Non-escaping let-fix inside a top-level fixpoint.
   The outer fixpoint gets loopified; the inner let-fix must have
   its type inferred for the loopification frame struct. *)
Fixpoint flat_map_sum (xss : list (list nat)) : nat :=
  match xss with
  | [] => 0
  | xs :: rest =>
    let fix inner_sum (ys : list nat) (acc : nat) : nat :=
      match ys with
      | [] => acc
      | y :: ys' => inner_sum ys' (acc + y)
      end
    in inner_sum xs 0 + flat_map_sum rest
  end.

(* Case 3: Nested let-fix — both should use auto *)
Definition flatten (ll : list (list nat)) : list nat :=
  let fix outer (xss : list (list nat)) : list nat :=
    match xss with
    | [] => []
    | xs :: rest =>
      let fix inner (ys : list nat) : list nat :=
        match ys with
        | [] => outer rest
        | y :: ys' => y :: inner ys'
        end
      in inner xs
    end
  in outer ll.

(* === Test values === *)

Definition test_sum : nat := sum_list [1; 2; 3; 4; 5].
Definition test_flat_map_sum : nat := flat_map_sum [[1; 2]; [3]; [4; 5; 6]].
Definition test_flatten : list nat := flatten [[10; 20]; [30]; [40; 50]].

End LetFixNoStdfun.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_no_stdfun" LetFixNoStdfun.
