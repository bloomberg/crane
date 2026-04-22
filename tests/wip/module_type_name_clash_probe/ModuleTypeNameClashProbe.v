From Crane Require Extraction.

Module ModuleTypeNameClashProbe.

Module M.
  Inductive t : Type := T : bool -> t.
End M.

Inductive M : Type := MkM : bool -> M.

Definition sample : bool :=
  match MkM true with
  | MkM b => b
  end.

End ModuleTypeNameClashProbe.

Crane Extraction "module_type_name_clash_probe" ModuleTypeNameClashProbe.
