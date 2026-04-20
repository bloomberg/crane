(* Rocq bug #3287: extraction of module with logical parts (I,I) *)

Require Crane.Extraction.

Module RocqBug3287.

Module Foo.
Definition bar := true.
End Foo.

Module Foo'.
Definition foo := (I,I).
Definition bar := true.
End Foo'.

Definition bar1 := Foo.bar.
Definition bar2 := Foo'.bar.

End RocqBug3287.

Crane Extraction "rocq_bug_3287" RocqBug3287.
