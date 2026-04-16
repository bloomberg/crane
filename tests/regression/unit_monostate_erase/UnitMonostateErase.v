(** Test for: Erase statement-only unit to void instead of std::monostate.

    These definitions exercise patterns where Rocq [unit] appears inside
    ITree programs as a discarded intermediate value.  Crane currently wraps
    some of them in [std::monostate]-returning IIFEs instead of lowering to
    plain [void] control flow. *)

From Corelib Require Import PrimString.
From Crane Require Import Mapping.Std Mapping.NatIntStd
  Monads.ITree Monads.IO.

Module UnitMonostateErase.

  (** --- Example 1: sequenced [if] returning unit ---

      The [if] result has type [itree ioE unit], but its value is discarded
      by [;;].  Crane should lower this to plain [if] control flow. *)
  Definition seq_if (b : bool) : itree ioE unit :=
    (if b then print_endline "yes" else Ret tt) ;;
    print_endline "done".

  (** --- Example 2: sequenced [if] where both branches are effects ---

      Both branches produce [itree ioE unit].  Should be a plain [if]. *)
  Definition seq_if_both (b : bool) : itree ioE unit :=
    (if b then print_endline "A" else print_endline "B") ;;
    print_endline "done".

  (** --- Example 3: tail-position match returning unit ---

      A match on a custom type, all branches [unit]-typed, in tail
      position of a void function. *)
  Inductive color := Red | Green | Blue.

  Definition match_unit_tail (c : color) : itree ioE unit :=
    match c with
    | Red   => Ret tt
    | Green => print_endline "green"
    | Blue  => print_endline "blue"
    end.

  (** --- Example 4: match inside bind --- *)
  Definition match_then_next (c : color) : itree ioE unit :=
    (match c with
     | Red   => Ret tt
     | Green => print_endline "green"
     | Blue  => print_endline "blue"
     end) ;;
    print_endline "after match".

  (** --- Example 5: chained sequenced ifs --- *)
  Definition chained_ifs (b1 b2 : bool) : itree ioE unit :=
    (if b1 then print_endline "b1" else Ret tt) ;;
    (if b2 then print_endline "b2" else Ret tt) ;;
    print_endline "end".

  (** --- Example 6: nested match-in-match --- *)
  Definition nested_matches (c1 c2 : color) : itree ioE unit :=
    (match c1 with
     | Red =>
       match c2 with
       | Red   => print_endline "RR"
       | Green => print_endline "RG"
       | Blue  => Ret tt
       end
     | Green => print_endline "G"
     | Blue  => Ret tt
     end) ;;
    print_endline "end".

End UnitMonostateErase.

Crane Extraction "unit_monostate_erase" UnitMonostateErase.
