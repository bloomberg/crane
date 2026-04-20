(* Rocq bug #14174: extraction error with sort-polymorphic singleton
   inductive type having Prop instance (sig2) in metacoq *)

Require Crane.Extraction.

Module RocqBug14174.

Module A.
  Include Corelib.Init.Specif.
End A.

End RocqBug14174.

Crane Extraction "rocq_bug_14174" RocqBug14174.
