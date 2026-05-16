(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: when a let-fix is hoisted to a top-level template function,
   the template argument at the call site must match the element type,
   not the full container type.
   Bug: Crane emits _go<List<unsigned int>>(...) instead of
        _go<unsigned int>(...), causing List<List<unsigned int>>
        in the parameter types. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LetFixHoistedTemplate.

(* reverse_onto: both params are list nat, return is list nat.
   Crane hoists the inner go to a top-level template and emits
   the wrong template argument at the call site. *)
Definition reverse_onto (l : list nat) : list nat :=
  let fix go (xs : list nat) (acc : list nat) : list nat :=
    match xs with
    | [] => acc
    | x :: rest => go rest (x :: acc)
    end
  in go l [].

(* === Test values === *)

Definition test_rev : list nat := reverse_onto [1; 2; 3].

End LetFixHoistedTemplate.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "let_fix_hoisted_template" LetFixHoistedTemplate.
