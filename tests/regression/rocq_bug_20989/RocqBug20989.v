(* Rocq bug #20989: extraction of module alias through functor application *)

Require Crane.Extraction.
From Crane Require Import Mapping.NatIntStd.

Module RocqBug20989.

Module Type S.
Definition n := 0.
End S.

Module A.
Definition n := 0.
End A.

Module M (X : S).
Module In := X.
Definition n := In.n.
End M.

Module N := M(A).

End RocqBug20989.

Crane Extraction "rocq_bug_20989" RocqBug20989.
