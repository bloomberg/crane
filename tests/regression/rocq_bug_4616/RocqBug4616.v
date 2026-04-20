(* Rocq bug #4616: primitive projections with Type field *)

Require Crane.Extraction.

Module RocqBug4616.

Set Primitive Projections.
Record Foo' := Foo { foo : Type }.
Definition f := forall t : Foo', foo t.

End RocqBug4616.

Crane Extraction "rocq_bug_4616" RocqBug4616.
