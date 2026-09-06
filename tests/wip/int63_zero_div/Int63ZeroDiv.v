(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The [PrimInt63] division, modulo and shift mappings in [Mapping/Std] guard
    their arguments with the wrong fallback: Rocq specifies [x mod 0 = x] and
    [x / 0 = 0], and a shift count of at least 63 gives 0.  The generated
    templates return 0 for the modulo case, so the extracted program silently
    disagrees with Rocq. *)
From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
From Stdlib Require Import Uint63.

Module Int63ZeroDiv.
Open Scope uint63_scope.
Definition d : int := 7 / 0.
Definition m : int := 7 mod 0.
Definition s : int := 1 << 70.
Definition run : int := d + m + s.
End Int63ZeroDiv.

Crane Extraction "int63_zero_div" Int63ZeroDiv.d Int63ZeroDiv.m Int63ZeroDiv.s Int63ZeroDiv.run.
