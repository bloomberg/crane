(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From ITree Require Import ITree.
Require Crane.Extraction.
Require Import Crane.Mapping.NatIntStd.

(** Factorial through coq-itree's [mrec]: each recursive call is an event
    [interp_mrec] answers by running the body again.  [interp_mrec] passes
    [iter] its step as a lambda, so it is the specialized interpreter that
    runs here. *)
Module MrecFact.

Variant call : Type -> Type := Fact (n : nat) : call nat.

Definition body : call ~> itree (call +' void1) :=
  fun _ c =>
    match c with
    | Fact n =>
      match n with
      | 0 => Ret 1
      | S m => ITree.bind (trigger (inl1 (Fact m))) (fun r => Ret (n * r))
      end
    end.

Definition fact (n : nat) : itree void1 nat := mrec body (Fact n).

End MrecFact.

Crane Extraction "mrec_fact" MrecFact.
