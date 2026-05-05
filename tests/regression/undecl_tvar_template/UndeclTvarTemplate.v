From Crane Require Extraction.
From Crane Require Import Mapping.Std.

Module Type Ty.
  Parameter Sigma : Type.
End Ty.

Module Make (X : Ty).
  Definition String := list X.Sigma.
  Definition String_dec {A : Type} (l : list A) (x : String) : bool :=
    match l with
    | nil => true
    | cons _ _ => false
    end.
End Make.

Crane Separate Extraction Make.
