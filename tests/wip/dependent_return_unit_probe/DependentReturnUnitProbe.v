From Crane Require Extraction.

Module DependentReturnUnitProbe.

Definition dep (b : bool) : if b then unit else bool :=
  match b with
  | true => tt
  | false => false
  end.

Definition sample_unit : unit := dep true.
Definition sample_bool : bool := dep false.

End DependentReturnUnitProbe.

Crane Extraction "dependent_return_unit_probe" DependentReturnUnitProbe.
