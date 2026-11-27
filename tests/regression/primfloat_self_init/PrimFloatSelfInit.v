(** [Mapping.Std] maps [PrimFloat.float] to [double] but leaves the primitive
    constants of that type unmapped, so each one extracts to a C++ constant
    initialised from itself:

      static inline const double infinity = infinity;

    which reads its own storage before it is initialised.  The program compiles
    and runs, and [infinity] and [nan] silently hold zero instead of the values
    they name. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
From Stdlib Require Import Floats.

Module PrimFloatSelfInit.
  Definition inf : float := infinity.
  Definition not_a_number : float := nan.
  Definition ordinary : float := 0.5.
End PrimFloatSelfInit.

Crane Extraction "primfloat_self_init" PrimFloatSelfInit.
