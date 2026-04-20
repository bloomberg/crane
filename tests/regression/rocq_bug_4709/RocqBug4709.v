(* Rocq bug #4709: extraction wasn't reducing primitive projections in types *)

Require Crane.Extraction.
From Crane Require Import Mapping.NatIntStd.

Module RocqBug4709.

Set Primitive Projections.

Record t := Foo { foo : Type }.
Definition ty := foo (Foo nat).

(* Without proper reduction of primitive projections in
   extract_type, the type ty was extracted incorrectly.
   We test that ty is properly reduced to nat. *)

Definition check : ty := 42.

End RocqBug4709.

Crane Extraction "rocq_bug_4709" RocqBug4709.
