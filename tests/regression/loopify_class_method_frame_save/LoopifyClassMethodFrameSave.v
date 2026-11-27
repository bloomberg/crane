From Crane Require Import Mapping.NatInt.
From Crane Require Extraction.
From Stdlib Require Import List.
Import ListNotations.
Set Crane Loopify.

(** Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
    testing of Crane: a generated program, shrunk by ephyra and reduced by hand.

    Under Loopify, a non-tail recursive call passed to a type-class method
    ([Nat.leb 1 (sz (g r))]) fails the ownership check under CRANE_CHECK_IR=1
    (the test suite's setting): "frame save: a frame save the plan decides
    keeps a local the C++ reading would move".  Without the check the C++ is
    right. *)
Module LoopifyClassMethodFrameSave.

Class Sz (A : Type) := { sz : A -> nat }.
#[global] Instance sz_bool : Sz bool := { sz b := if b then 1 else 0 }.

Fixpoint g (l : list nat) : bool :=
  match l with [] => true | _ :: r => Nat.leb 1 (sz (g r)) end.

(** Two method calls nested on the recursive result, [sz (sz (h m))]: the
    frame keeps both instance fields, and the outer one, read once the let
    binding the call's result is done, was planned as kept where the C++
    reading moves it ("frame save", as above). *)
#[global] Instance sz_nat : Sz nat := { sz n := S n }.

Fixpoint h (n : nat) : nat := match n with 0 => 0 | S m => sz (sz (h m)) end.

End LoopifyClassMethodFrameSave.

Crane Extraction "loopify_class_method_frame_save" LoopifyClassMethodFrameSave.
