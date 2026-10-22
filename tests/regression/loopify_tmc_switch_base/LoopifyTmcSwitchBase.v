From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Set Crane Loopify.

(** A base case of a tail-modulo-cons loop inside an enum's match.

    Tail modulo cons builds the result in a [while (true)] loop and leaves it
    from a base case by [break], once the base value is in place.  A match on
    an enum is a [switch], where [break] leaves only the switch: the loop went
    round again on the same input and never returned.  [f Blue] reaches a base
    case at once, inside the switch; [f Red] and [f Green] reach one through
    the recursion, the second nested in a match inside the switch. *)

Module LoopifyTmcSwitchBase.

Inductive num := Z | Su (n : num).

Inductive color := Red | Green | Blue.

Fixpoint f (c : color) (n : num) : num :=
  match n with
  | Z => Z
  | Su m =>
    match c with
    | Red => f Green m
    | Green => Su (f Blue m)
    | Blue => match m with Z => Su (Su Z) | Su _ => f Red m end
    end
  end.

Fixpoint of_nat (n : nat) : num := match n with O => Z | S m => Su (of_nat m) end.

Fixpoint to_nat (n : num) : nat := match n with Z => O | Su m => S (to_nat m) end.

Definition run_f (c : color) (n : nat) : nat := to_nat (f c (of_nat n)).

End LoopifyTmcSwitchBase.

Crane Extraction "loopify_tmc_switch_base" LoopifyTmcSwitchBase.
