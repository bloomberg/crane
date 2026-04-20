(* Rocq bug #4844 (and #4824): extraction confusion between unknown
   and dummy types with logical parts *)

Require Crane.Extraction.

Module RocqBug4844.

Definition semilogic : True + True := inl I.

Record SomeType := { ST : Type }.

Definition SomeTrue := {| ST := True |}.

Definition abstrSum (t : SomeType) := ((ST t) + (ST t))%type.

Definition semilogic' : abstrSum SomeTrue := semilogic.

Inductive box (t : SomeType) := Box : ST t + ST t -> box t.

Definition boxed_semilogic : box SomeTrue :=
 Box SomeTrue semilogic.

End RocqBug4844.

Crane Extraction "rocq_bug_4844" RocqBug4844.
