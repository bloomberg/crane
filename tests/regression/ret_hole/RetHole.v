(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [%ret] in an inline mapping spells the type the call yields, as
    translation recorded it.  Only a template applied as a call yields one:
    a block template ([%result]) naming [%ret] is refused before anything is
    printed, where it used to leave the placeholder in the C++ text. *)

From Crane Require Import Extraction.
From Crane.Mapping Require Import Std NatIntStd.

Axiom double : nat -> nat.
Crane Extract Inlined Constant double => "static_cast<%ret>(2 * %a0)".

Module RetHole.

Definition quadruple (n : nat) : nat := double (double n).

End RetHole.
Crane Extraction "ret_hole" RetHole.

Axiom halve : nat -> nat.
Crane Extract Inlined Constant halve => "%result = static_cast<%ret>(%a0 / 2)".

Module RetInBlock.

Definition quarter (n : nat) : nat := halve (halve n).

End RetInBlock.
Fail Crane Extraction "ret_hole_in_block" RetInBlock.
