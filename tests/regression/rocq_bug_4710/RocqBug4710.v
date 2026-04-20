(* Rocq bug #4710: extraction of primitive projections *)

Require Crane.Extraction.
From Crane Require Import Mapping.NatIntStd.

Module RocqBug4710.

Set Primitive Projections.
Record Foo' := Foo { foo : nat }.

Record Foo2 (a : nat) := Foo2c { foo2p : nat; foo2b : bool }.

Definition bla (x : Foo2 0) := foo2p _ x.

Definition bla' (a : nat) (x : Foo2 a) := foo2b _ x.

Definition test_foo := Foo 5.
Definition test_foo2 := Foo2c 0 10 true.
Definition test_bla := bla test_foo2.
Definition test_bla' := bla' 0 test_foo2.

End RocqBug4710.

Crane Extraction "rocq_bug_4710" RocqBug4710.
