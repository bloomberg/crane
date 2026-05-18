(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: when a let-fix body binds intermediate values via let,
   those bindings should use const-ref where possible to avoid
   unnecessary copies of inductive values. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixIntermediateRef.

(* sum_heads: for each sublist, extract the head element and sum them.
   The intermediate hd binding should reference the head value
   without copying the entire sublist. *)
Definition sum_heads (ll : list (list nat)) : nat :=
  let fix go (xss : list (list nat)) (acc : nat) : nat :=
    match xss with
    | [] => acc
    | xs :: rest =>
      let hd := match xs with
                | [] => 0
                | x :: _ => x
                end
      in go rest (acc + hd)
    end
  in go ll 0.

(* zip_sum: traverse two lists in parallel, sum corresponding elements.
   Both list params are borrowed, intermediate bindings should be refs. *)
Fixpoint zip_sum (l1 l2 : list nat) : nat :=
  match l1, l2 with
  | x :: r1, y :: r2 => (x + y) + zip_sum r1 r2
  | _, _ => 0
  end.

(* === Test values === *)

Definition test_heads : nat := sum_heads [[10; 20]; [30]; []; [40; 50]].
Definition test_zip : nat := zip_sum [1; 2; 3] [10; 20; 30].

End LetFixIntermediateRef.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_intermediate_ref" LetFixIntermediateRef.
