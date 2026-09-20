(* Expected: [go] returns 3.
   Actual:   the emitted [cmp] is an infinite loop.

   THIS IS NOT A COMPILE ERROR.  The translation unit builds; the program
   hangs.  A tail call to a function with the SAME basename in a DIFFERENT
   module is loopified as if it were a self-call, so the actual callee
   disappears and the loop has no exit:

     while (true) {
       _loop_x = M1::to1(_loop_x);   // the conversion, kept
       ...                            // the call to M1::cmp, gone
     }

   Found in Vellvm via Flocq [IEEE754/Binary.v:773]:

     Definition Bcompare (f1 f2 : binary_float) : option comparison :=
       BinarySingleNaN.Bcompare (B2BSN f1) (B2BSN f2).

   whose emitted body is a [while (true)] with no [break] and no [return].
   Vellvm reaches it through float comparison, so [fcmp] on any program hits
   it.  The two [no viable overloaded '='] errors at that site are incidental
   -- a missed collision rename on [B2BSN]'s return type -- and correcting
   them makes the function compile and hang.  Do not fix this as a type error.

   Discriminator: Flocq's [Bmult] makes the same same-name-different-module
   call and comes out correct, because it is wrapped in [BSN2B] and so is not
   in tail position.  Tail position plus a matching basename is the trigger.

   The [alarm] in the .t.cpp is what keeps a hang from wedging the suite. *)

From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module TailCallSameNameOtherModule.

  Module T1.
    Inductive t1 : Set := Z1 | C1 : nat -> t1.
    Definition cmp (x : t1) (y : t1) : nat :=
      match x, y with
      | Z1, _ => 0
      | _, Z1 => 0
      | C1 a, C1 b => a + b
      end.
  End T1.

  Module T2.
    Inductive t2 : Set := Z2 | C2 : nat -> t2.
    Definition to1 (x : t2) : T1.t1 :=
      match x with Z2 => T1.Z1 | C2 n => T1.C1 n end.

    (* Tail call to [T1.cmp]: same basename, different module. *)
    Definition cmp (x y : t2) : nat := T1.cmp (to1 x) (to1 y).
  End T2.

  Definition go : nat := T2.cmp (T2.C2 1) (T2.C2 2).

  Definition ok : bool := Nat.eqb go 3.

End TailCallSameNameOtherModule.

Crane Extraction "tail_call_same_name_other_module" TailCallSameNameOtherModule.
