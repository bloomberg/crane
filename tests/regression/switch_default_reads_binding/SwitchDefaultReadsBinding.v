From Crane Require Import Extraction.

(** A binding read only in a switch's [default] arm: dead-binding removal
    must see the arm, or the declaration goes and the arm names nothing. *)
Module SwitchDefaultReadsBinding.

Inductive color := Red | Green | Blue | Black.

Inductive shade := Shade (a b : color).

Definition pick (c : color) : shade :=
  let k := Green in
  match c with
  | Red => Shade Red Red
  | _ => Shade k k
  end.

End SwitchDefaultReadsBinding.

Crane Extraction "switch_default_reads_binding" SwitchDefaultReadsBinding.
