(* Rocq bug #20894: extraction of axiom with sealed module type *)

Require Crane.Extraction.

Module RocqBug20894.

Module Type S.
  Parameter t : Type.
  Parameter fold : t.
End S.

Module M : S.
  Definition t := list unit -> unit.
  Fixpoint fold (l : list unit) : unit :=
    match l with
    | nil => tt
    | cons b l =>
      match b with
      | tt => fold l
      end
    end.
End M.

Axiom bug : M.t.

End RocqBug20894.

Crane Extraction "rocq_bug_20894" RocqBug20894.
