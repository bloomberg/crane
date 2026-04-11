From Crane Require Import Mapping.Std.
From Crane Require Extraction.

Module OptionLetNoneBug.

Definition bug : option bool :=
  let e := @None bool in
  e.

End OptionLetNoneBug.

Crane Extraction "option_let_none_bug" OptionLetNoneBug.
