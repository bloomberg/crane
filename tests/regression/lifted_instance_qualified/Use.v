From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import String.
From CraneTestsRegression Require lifted_instance_qualified.StringUtil.
From CraneTestsRegression Require lifted_instance_qualified.Other.

Module LiftedInstanceQualified.
  Definition use (n : nat) : string :=
    (Other.banner ++ StringUtil.banner ++ @StringUtil.show nat StringUtil.showN n)%string.
End LiftedInstanceQualified.

Crane Extraction "lifted_instance_qualified" LiftedInstanceQualified.
