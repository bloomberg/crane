(* Rocq bug #5177: extraction and module type containing application
   and "with" *)

Require Crane.Extraction.

Module RocqBug5177.

Module Type T.
  Parameter t : Type.
End T.

Module Type A (MT : T).
  Parameter t1 : Type.
  Parameter t2 : Type.
  Parameter bar : MT.t -> t1 -> t2.
End A.

Module MakeA(MT : T) : A MT with Definition t1 := nat.
  Definition t1 := nat.
  Definition t2 := nat.
  Definition bar (m : MT.t) (x : t1) := x.
End MakeA.

End RocqBug5177.

Crane Extraction "rocq_bug_5177" RocqBug5177.
