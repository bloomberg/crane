From Stdlib Require Import List.
Import ListNotations.
From CraneTestsRegression Require Import instance_uses_earlier_member.IuMemIface.
Section Implementation.
  Context {Pa : Params}.
  Record St : Type := mkSt { mem : list ptr }.
  Definition empty_st : St := mkSt [zero].
  Instance StateV : @MemState Pa :=
    { state := St ; initial_state := empty_st ; size_of := fun s => length (mem s) }.
  Definition get_size : memM nat := fun s => (s, size_of s).
  Definition get_size2 : memM nat := fun s => get_size s.
End Implementation.
