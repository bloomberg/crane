From Crane Require Extraction.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List.

(** Eliminators applied directly are lifted into anonymous helpers, and every
    one of them is named [_anon_F].  Two in the same file collide — here
    [nat_rect] and [list_rect] become one overload set and neither call
    matches — and one used from a sibling module is not visible there at all
    ("use of undeclared identifier '_anon_F'").  A single lifted helper in a
    single module works, so the defect is the name, not the lifting. *)

Module Helper.
  Definition count : nat := nat_rect (fun _ => nat) 0 (fun _ r => S r) 3.
End Helper.

Module AnonLiftNameCollision.
  Definition run : nat :=
    Helper.count + list_rect (fun _ => nat) 0 (fun _ _ r => S r) (cons 1 nil).
End AnonLiftNameCollision.

Crane Extraction "anon_lift_name_collision" AnonLiftNameCollision.
