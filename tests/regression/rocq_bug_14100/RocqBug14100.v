(* Rocq bug #14100: extraction of variant/inductive types
   assigned to module type parameters *)

Require Crane.Extraction.

Module RocqBug14100.

Variant nondetE : Type -> Type :=
  Or : nondetE bool.

Module Type MinSIG.
Parameter otherE : Type -> Type.
End MinSIG.

Module Min : MinSIG.
Definition otherE := nondetE.
End Min.

End RocqBug14100.

Crane Extraction "rocq_bug_14100" RocqBug14100.
