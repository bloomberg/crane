(** Crane bug, found by Ephyra round 31: an [option] mapped to
    [std::optional] (Mapping.Std) passed through [id], which is declared at
    [crane::obj].  The value is built at the canonical erased shape,
    [std::make_optional<crane::obj>(...)], and read back with a strict
    [crane::any_cast<std::optional<uint64_t>>]: [bad_any_cast] at run time.
    Expected: [m = 4].  Present at 081553f85. *)
From Crane Require Extraction.
From Crane Require Import Mapping.NatInt Mapping.Std.

Module IdMappedOptionShape.

Definition fo (o : option nat) : nat := match o with Some k => k | None => 2 end.
Definition m : nat := fo (id (Some 4)).

End IdMappedOptionShape.

Crane Extraction "id_mapped_option_shape" IdMappedOptionShape.
