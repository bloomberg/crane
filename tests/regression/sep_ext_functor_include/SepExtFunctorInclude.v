From Crane Require Import Mapping.Std.
From Crane Require Extraction.
From CraneTestsRegression Require Import sep_ext_functor_include.Ord.

(** A functor whose parameter's concept and whose body's functor
    application both come from another file: its header must include that
    file's, though nothing generated ahead of the files names it. *)
Module Tac (O : Ordered).
  Module F := Full O.
  Definition gtb (x y : O.t) : bool := negb (F.geb y x).
End Tac.

Module NatOrd <: Ordered.
  Definition t := nat.
  Definition leb := Nat.leb.
End NatOrd.

Module T := Tac NatOrd.

Definition gt_two_one : bool := T.gtb 2 1.

Crane Separate Extraction gt_two_one.
