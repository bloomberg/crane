From Crane Require Extraction.
From ExtLib Require Import Structures.Monads.
From CraneTestsWIP Require instance_used_before_defined.Lib.

Import MonadNotation.
Open Scope monad.

(* A *record* of operations -- so the value below is a struct literal with
   std::function fields, the shape of Vellvm's [VMemInt_Z]. *)
Record Arith (I : Type) : Type := { madd : I -> I -> Lib.EOU I ; mzero : I }.
Arguments madd {I}.

(* A global whose only reference to [EOU_monad] is inside a lambda in its
   initializer. *)
Definition Arith_nat : Arith nat :=
  {| madd x y := ret (x + y) ; mzero := 0 |}.
