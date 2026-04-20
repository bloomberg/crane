(* Rocq bug #3923: functor extraction leading to uncaught Not_found *)

Require Crane.Extraction.

Module RocqBug3923.

Module Type TRIVIAL.
Parameter t : Type.
End TRIVIAL.

Module MkStore (Key : TRIVIAL).

Module St : TRIVIAL.
Definition t := unit.
End St.

End MkStore.

Module Type CERTRUNTIMETYPES (B : TRIVIAL).

Parameter cert_fieldstore : Type.
Parameter empty_fieldstore : cert_fieldstore.

End CERTRUNTIMETYPES.

Module MkCertRuntimeTypes (B : TRIVIAL) : CERTRUNTIMETYPES B.

Module FieldStore := MkStore B.

Definition cert_fieldstore := FieldStore.St.t.
Axiom empty_fieldstore : cert_fieldstore.

End MkCertRuntimeTypes.

End RocqBug3923.

Crane Extraction "rocq_bug_3923" RocqBug3923.
