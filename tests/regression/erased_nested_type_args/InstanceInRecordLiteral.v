From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From ExtLib Require Import Structures.Monads.

Import MonadNotation.
Open Scope monad.

Variant EOU {X : Type} : Type :=
  | raise_error (s : nat) : EOU
  | raise_ret (x : X) : EOU.
Arguments EOU : clear implicits.

#[global] Instance EOU_monad : Monad EOU :=
  {| ret := @raise_ret ;
     bind _ _ c k :=
       match c with
       | raise_error s => raise_error s
       | raise_ret x => k x
       end
  |}.

(* A record of operations, the shape of Vellvm's [VMemInt]. *)
Class Ops (I : Type) : Type := { madd : I -> I -> EOU I ; mzero : I }.

(* The only reference to [EOU_monad] is inside a lambda in this global
   record literal. *)
#[global] Instance Ops_nat : Ops nat :=
  {| madd x y := ret (x + y) ; mzero := 0 |}.

Module InstanceInRecordLiteral.
  Definition use (n : nat) : EOU nat := @madd nat Ops_nat n n.
End InstanceInRecordLiteral.

Crane Extraction "instance_in_record_literal" InstanceInRecordLiteral.
