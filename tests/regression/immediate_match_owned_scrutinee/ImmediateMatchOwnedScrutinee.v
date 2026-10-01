From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List.
Import ListNotations.

(** A [match] in argument position becomes an immediately invoked lambda,
    [std::make_optional<Nat>([...]() { ... n.v_mut() ... }())].  The
    scrutinee [n] is an owned local, so the match destructures it through
    [v_mut()].  [return_captures_by_value] made that lambda a [Closure]
    because it sits in a returned expression, and a closure's captures are
    [const] since a0357147d, so [v_mut()] on the captured [Nat] did not
    compile.  A lambda invoked where it is written is never stored: it stays
    [Immediate] and captures by reference.  Found in Vellvm's
    [FMapFacts.cardinal_inv_2b]. *)

Module ImmediateMatchOwnedScrutinee.

  Fixpoint count (l : list nat) : nat := match l with [] => O | _ :: r => S (count r) end.

  Definition pred_count (l : list nat) : option nat :=
    let n := count l in
    let g := fun k => count (k :: l) in
    Some (match n with
          | O => O
          | S k => g k
          end).

  Definition check (_ : unit) : bool :=
    match pred_count [1; 2; 3] with Some (S (S (S (S O)))) => true | _ => false end.

End ImmediateMatchOwnedScrutinee.

Crane Extraction "immediate_match_owned_scrutinee" ImmediateMatchOwnedScrutinee.
