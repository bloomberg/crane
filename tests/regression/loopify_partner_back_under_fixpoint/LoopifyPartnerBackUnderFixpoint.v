From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

(** [tree_size]'s partner [forest_size] calls it back only from a local
    fixpoint over a list of trees, and [tree_size] calls [forest_size] as
    the operand of an addition.  No machine can enter [forest_size], so its
    body runs in place of the call, its calls of [tree_size] ordinary calls,
    as a call of [forest_size] would make them. *)

Module LoopifyPartnerBackUnderFixpoint.

  Inductive tree := Node (n : nat) (kids : forest)
  with forest := Forest (ts : list tree).

  Fixpoint tree_size (t : tree) : nat :=
    match t with
    | Node n kids => n + forest_size kids
    end
  with forest_size (f : forest) : nat :=
    match f with
    | Forest ts =>
        (fix sizes (l : list tree) : nat :=
           match l with
           | nil => 0
           | cons t rest => tree_size t + sizes rest
           end) ts
    end.

  Fixpoint chain (k : nat) (t : tree) : tree :=
    match k with
    | O => t
    | S k' => chain k' (Node 1 (Forest (cons t (cons (Node 1 (Forest nil)) nil))))
    end.

End LoopifyPartnerBackUnderFixpoint.

Set Crane Loopify.
Crane Extraction "loopify_partner_back_under_fixpoint" LoopifyPartnerBackUnderFixpoint.
