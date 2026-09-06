From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.ZInt.
From Stdlib Require Import BinInt.
Open Scope Z_scope.

(** [ZInt] expands [Z.div] and [Z.modulo] into an immediately-invoked lambda
    that adjusts C++ truncation to Rocq's flooring.  That lambda is written
    [[&]], which C++ forbids for a lambda at class or namespace scope -- and a
    top-level [Definition] is initialised exactly there.  [Mapping.DequeList]'s
    [List.rev] has the same shape and the same failure. *)

Module MappingLambdaCaptureDefault.

  Definition d : Z := Z.div (-7) 2.
  Definition m : Z := Z.modulo (-7) 2.

  Definition run : Z := d * 10 + m.

End MappingLambdaCaptureDefault.

Crane Extraction "mapping_lambda_capture_default" MappingLambdaCaptureDefault.
