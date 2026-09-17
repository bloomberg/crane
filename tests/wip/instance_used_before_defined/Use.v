From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From CraneTestsWIP Require instance_used_before_defined.Lib.
From CraneTestsWIP Require instance_used_before_defined.Ops.

Module InstanceUsedBeforeDefined.
  Definition use (n : nat) : Lib.EOU nat := Ops.madd Ops.Arith_nat n n.
End InstanceUsedBeforeDefined.

Crane Extraction "instance_used_before_defined" InstanceUsedBeforeDefined.
