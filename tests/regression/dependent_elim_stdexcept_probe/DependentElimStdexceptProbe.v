From Crane Require Extraction.

Module DependentElimStdexceptProbe.

Inductive avail : bool -> Type :=
| Present : avail true
| Absent : avail false.

Definition get_present (a : avail true) : unit :=
  match a with
  | Present => tt
  end.

Definition sample : unit := get_present Present.

End DependentElimStdexceptProbe.

Crane Extraction "dependent_elim_stdexcept_probe" DependentElimStdexceptProbe.
