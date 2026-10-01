(** Crane bug: a type from a sibling top-level module ([Module Ev], a
    struct at file scope in the header) is qualified as if it were nested in
    the extracted module in out-of-line definitions.

    Observed (post-interp_state_after_interp HEAD):
      SiblingModuleQualified::Ev::Color SiblingModuleQualified::flip(...)
    Diagnostic:
      error: no member named 'Ev' in 'SiblingModuleQualified'; did you mean simply 'Ev'?

    Found while reducing a Vellvm runtime issue (the same happens with an
    event module next to the extracted one); not currently on Vellvm's
    path. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

(* A sibling top-level module whose type is used by the extracted module. *)
Module Ev.
  Inductive color : Type := Red | Green.
End Ev.
Import Ev.

Module SiblingModuleQualified.
  Definition flip (c : color) : color := match c with Red => Green | Green => Red end.
  Definition count (c : color) (n : nat) : nat := match flip c with Red => n | Green => S n end.
  Definition is_one : bool := Nat.eqb (count Red 0) 1.
End SiblingModuleQualified.

Crane Extraction "sibling_module_qualified" SiblingModuleQualified.
