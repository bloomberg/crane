(* Rocq bug #14843: record projection name conflicts with module definitions
   (f1 renamed to Coq__1.f1 but Coq__1 was not defined) *)

Require Crane.Extraction.

Module RocqBug14843.

Record r : Type := mk { f1 : unit -> unit; f2 : unit -> unit }.
Set Primitive Projections.
Record r' : Type := mk' { f1' : unit -> unit; f2' : unit -> unit }.
Unset Primitive Projections.

Module M.
Definition f1 (ti : unit) : unit := tt.
Definition f2 (ti : unit) : unit := tt.
Definition cf := mk f1 f2.

Definition f1' (ti : unit) : unit := tt.
Definition f2' (ti : unit) : unit := tt.
Definition cf' := mk' f1' f2'.
End M.

End RocqBug14843.

Crane Extraction "rocq_bug_14843" RocqBug14843.
