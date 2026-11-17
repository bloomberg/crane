From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [sum_e] calls its partner [sum_md] as an operand, and [sum_md] calls
    [sum_e] back, so [sum_e]'s machine would enter a copy of [sum_md] -- but
    [sum_md] also calls itself inside the closure it folds a list with, and
    the copy a machine enters is no value a closure could call.  Its body
    runs in place of the call instead. *)

Module LoopifyPartnerSelfInClosure.

  Inductive e := Leaf (n : nat) | Meta (m : md)
  with md := MNil | MNode (l : list md) | MConst (x : e).

  Fixpoint sum_e (x : e) : nat :=
    match x with
    | Leaf n => n
    | Meta m => 1 + sum_md m
    end
  with sum_md (m : md) : nat :=
    match m with
    | MNil => 0
    | MNode l => fold_left (fun acc m => acc + sum_md m) l 0
    | MConst x => sum_e x
    end.

  (** 1 + (2 + (1 + 3)) *)
  Definition check (_ : unit) : bool :=
    Nat.eqb (sum_e (Meta (MNode [MConst (Leaf 2); MConst (Meta (MConst (Leaf 3))); MNil]))) 7.

End LoopifyPartnerSelfInClosure.

Set Crane Loopify.
Crane Extraction "loopify_partner_self_in_closure" LoopifyPartnerSelfInClosure.
