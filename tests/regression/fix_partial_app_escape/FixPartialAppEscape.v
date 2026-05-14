(* Regression: a fixpoint that is partially applied escapes its
   defining scope.  The fixpoint body must not capture the
   std::function variable by reference ([&]) because the IIFE
   returns a lambda that outlives the stack frame.  Previously
   Crane used gen_local_fix_by_ref for all applied fixpoints,
   causing a dangling reference and crash at runtime.

   This test reproduces the ascii_of_pos pattern: a fixpoint
   with 2 params partially applied to 1 arg. *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module FixPartialAppEscape.

  (* A fixpoint with 2 parameters, partially applied to 1 *)
  Definition count_bits : nat -> nat :=
    (fix go (depth : nat) (n : nat) : nat :=
       match depth with
       | O => O
       | S d =>
         match n with
         | O => O
         | S _ => S (go d (Nat.div n 2))
         end
       end) 32.

  Definition test_0 := count_bits 0.
  Definition test_1 := count_bits 1.
  Definition test_7 := count_bits 7.
  Definition test_255 := count_bits 255.

End FixPartialAppEscape.

Crane Extraction "fix_partial_app_escape" FixPartialAppEscape.
