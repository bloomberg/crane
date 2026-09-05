From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.
Require Import List.
Import ListNotations.

Module NatLiteralOverflow.

(** [nat] maps onto [uint64_t], so a literal is only extractable if it fits.
    The largest one that does still comes through exactly. *)
Definition max64 : nat := 18446744073709551615.

Definition small : nat := 5.

Definition total : nat := small + small.

End NatLiteralOverflow.
Crane Extraction "nat_literal_overflow" NatLiteralOverflow.

Module TooBig.

(** One past [uint64_t]'s range.  Emitting it verbatim would leave an
    out-of-range literal in the header for the C++ compiler to trip over, so
    extraction rejects it while the Rocq definition can still be named. *)
Definition big : nat := 18446744073709551616.

End TooBig.
Fail Crane Extraction "nat_literal_overflow_too_big" TooBig.

Module WayTooBig.
Definition bigger : nat := 100000000000000000000000.
End WayTooBig.
Fail Crane Extraction "nat_literal_overflow_way_too_big" WayTooBig.
