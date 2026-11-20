(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Local let-fix — fix bound inside a definition body. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFix.

(* let fix inside a definition *)
Definition local_sum (l : list nat) : nat :=
  let fix go (acc : nat) (xs : list nat) : nat :=
    match xs with
    | [] => acc
    | x :: rest => go (acc + x) rest
    end
  in go 0 l.

(* let fix with accumulator pattern *)
Definition local_rev {A : Type} (l : list A) : list A :=
  let fix go (acc : list A) (xs : list A) : list A :=
    match xs with
    | [] => acc
    | x :: rest => go (x :: acc) rest
    end
  in go [] l.

(* Nested let fix *)
Definition local_flatten (ll : list (list nat)) : list nat :=
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

(* let fix returning bool *)
Definition local_mem (n : nat) (l : list nat) : bool :=
  let fix go (xs : list nat) : bool :=
    match xs with
    | [] => false
    | x :: rest => if Nat.eqb x n then true else go rest
    end
  in go l.

(* let fix with two recursive calls *)
Definition local_length {A : Type} (l : list A) : nat :=
  let fix go (xs : list A) : nat :=
    match xs with
    | [] => 0
    | _ :: rest => S (go rest)
    end
  in go l.

(* === Test values === *)

Definition test_sum : nat := local_sum [1; 2; 3; 4; 5].
Definition test_rev : list nat := local_rev [1; 2; 3].
Definition test_flatten : list nat := local_flatten [[1; 2]; [3]; [4; 5; 6]].
Definition test_mem_found : bool := local_mem 3 [1; 2; 3; 4].
Definition test_mem_missing : bool := local_mem 9 [1; 2; 3; 4].
Definition test_length : nat := local_length [10; 20; 30; 40].

End LetFix.

Require Crane.Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix" LetFix.
