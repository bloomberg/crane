(* Collides with [StringUtil.parens], forcing both files to become structs. *)
From Crane Require Extraction.
From Stdlib Require Import String.

Definition parens (s : string) : string := ("[" ++ s ++ "]")%string.
Definition banner : string := "o"%string.
