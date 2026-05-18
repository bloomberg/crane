(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: traversing a List<List<T>> via let-fix should not deep-clone
   inner lists when only destructuring the outer spine.
   With const-ref params, the outer traversal binds references to
   the inner lists rather than copying them. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixNestedClone.

(* sum_nested: traverse outer list, sum each inner list.
   The outer list param should be const-ref (borrowed).
   Each inner list is accessed by reference through the outer Cons. *)
Definition sum_nested (ll : list (list nat)) : nat :=
  let fix outer (xss : list (list nat)) (acc : nat) : nat :=
    match xss with
    | [] => acc
    | xs :: rest =>
      let fix inner (ys : list nat) (a : nat) : nat :=
        match ys with
        | [] => a
        | y :: ys' => inner ys' (a + y)
        end
      in outer rest (inner xs 0 + acc)
    end
  in outer ll 0.

(* count_nested: count total elements across nested lists *)
Definition count_nested (ll : list (list nat)) : nat :=
  let fix outer (xss : list (list nat)) (acc : nat) : nat :=
    match xss with
    | [] => acc
    | xs :: rest =>
      let fix inner (ys : list nat) (n : nat) : nat :=
        match ys with
        | [] => n
        | _ :: ys' => inner ys' (1 + n)
        end
      in outer rest (inner xs 0 + acc)
    end
  in outer ll 0.

(* === Test values === *)

Definition test_sum : nat := sum_nested [[1; 2]; [3]; [4; 5; 6]].
Definition test_count : nat := count_nested [[1; 2]; [3]; [4; 5; 6]].

End LetFixNestedClone.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_nested_clone" LetFixNestedClone.
