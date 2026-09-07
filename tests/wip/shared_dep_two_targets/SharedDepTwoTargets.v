(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Import Mapping.NatIntStd Mapping.Std.

(** Two extraction targets that both depend on a definition outside either of
    them each emit their own copy of it.  The two headers are individually
    well-formed, but a translation unit that includes both sees [Col] defined
    twice.  Nothing in the generated code marks the copies as the same entity. *)

Inductive Col := Red | Green.

Definition flip (c : Col) : Col := match c with Red => Green | Green => Red end.

Module SharedDepTwoTargets.

  Definition test : bool :=
    match flip Red with Green => true | Red => false end.

End SharedDepTwoTargets.

Module SharedDepTwoTargetsB.

  Definition test2 : bool :=
    match flip Green with Red => true | Green => false end.

End SharedDepTwoTargetsB.

Crane Extraction "shared_dep_two_targets" SharedDepTwoTargets.
Crane Extraction "shared_dep_two_targets_b" SharedDepTwoTargetsB.
