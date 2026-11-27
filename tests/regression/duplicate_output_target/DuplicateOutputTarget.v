(** Two [Crane Extraction] commands naming the same output file used to
    silently overwrite one another: the second unit's header and implementation
    replaced the first's, with no warning, so the declarations of the first
    module were simply gone.  The second command is now refused; the modules
    have to be named in one command, or given targets of their own.

    The substantive assertions run while DuplicateOutputTarget.vo is built. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.

Module First.
  Definition one : nat := 1.
End First.

Module Second.
  Definition two : nat := 2.
End Second.

Crane Extraction "duplicate_output_target" First Second.

(* A second extraction to a target already claimed is refused. *)
Fail Crane Extraction "duplicate_output_target" Second.
