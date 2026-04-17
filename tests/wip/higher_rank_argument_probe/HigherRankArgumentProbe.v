From Crane Require Extraction.

Module HigherRankArgumentProbe.

Definition call_poly (f : forall A : Type, A -> A) : bool :=
  f bool true.

Definition sample : bool :=
  call_poly (fun A x => x).

End HigherRankArgumentProbe.

Crane Extraction "higher_rank_argument_probe" HigherRankArgumentProbe.
