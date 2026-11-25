(** Rocq bug #3287: extraction of module with logical parts (I,I).

    Extracting the whole module used to fail with "The informative inductive
    type prod has a Prop instance": [Foo'.foo : True * True] is a proposition
    only through template-polymorphic [prod] instantiated at [Prop], and the
    strict sort computation ([~polyprop:false]) raises on it.  Fixed: a
    declaration's own flag is computed by [declaration_flag] in
    src/rocq_to_core/extraction.ml, which on that error retries with
    [~polyprop:true] and erases the declaration whole when it is logical.  A
    use that eliminates [Foo'.foo] into [Type] still reports the error. *)

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
