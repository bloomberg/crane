From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module Type S.
  Parameter t : Type.
  Parameter zero : t.
  Parameter to_nat : t -> nat.
End S.

Module F (X : S).
  Definition value : nat := X.to_nat X.zero.
End F.

Module N <: S.
  Definition t := nat.
  Definition zero := 0.
  Definition to_nat (n : nat) := n.
End N.

Module FN := F N.

Module FunctorOutputProbe.
  Definition sample : nat := FN.value.
End FunctorOutputProbe.

Crane Extraction "functor_output_probe" FunctorOutputProbe.
