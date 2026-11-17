(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** [Crane Show Extraction] renders the term of the proof in progress as the
    one declaration of a unit of its own.  It planned an empty unit instead,
    so the declaration it rendered had no callable plan, and neither did a
    global the term calls: every use was an anomaly.  The command runs while
    this file is compiled, so an anomaly fails the test. *)

Module ShowExtractionPlanned.
  Definition twice (n : nat) : nat := n + n.

  Definition four : nat := twice 2.
End ShowExtractionPlanned.

Require Crane.Extraction.
From Crane Require Mapping.Std.

Lemma shown : nat -> nat.
Proof.
  intro n. exact (S (ShowExtractionPlanned.twice n)).
  Crane Show Extraction.
Defined.

Crane Extraction "show_extraction_planned" ShowExtractionPlanned.
