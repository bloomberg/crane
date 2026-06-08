From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Module Type Sigma.
  Parameter Sigma : Type.
  Parameter Sigma_dec : forall a a' : Sigma, {a = a'} + {a <> a'}.
End Sigma.

Module DefsFn (Ty : Sigma).
  Module Strings.
    Definition String : Type := list Ty.Sigma.

    Lemma String_dec : forall s s' : String, {s = s'} + {s <> s'}.
    Proof. decide equality. apply Ty.Sigma_dec. Qed.
  End Strings.
End DefsFn.

Crane Separate Extraction DefsFn.
