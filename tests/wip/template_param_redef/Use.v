From Crane Require Extraction.
From CraneTestsWIP Require Import template_param_redef.Lib.

Module M.
  Definition use {A : Type} (b : ex A) : unit := f b.
End M.

Crane Extraction "template_param_redef" M.
