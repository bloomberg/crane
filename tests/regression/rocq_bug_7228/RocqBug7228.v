(* Rocq bug #7228: extraction with conservative types and dependent match *)

Require Crane.Extraction.

Module RocqBug7228.

Inductive data := Data : forall (T : Type), T -> data.
Definition t_of d := match d with Data t _ => t end.
Definition v_of (d : data) := match d return t_of d with Data _ v => v end.

Definition test_data := Data nat 42.

End RocqBug7228.

Crane Extraction "rocq_bug_7228" RocqBug7228.
