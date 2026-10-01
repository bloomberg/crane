From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
From Stdlib Require Import List.
Import ListNotations.

(** [dbl_e] and [dbl_md] are mutually recursive and return different types
    ([e] and [md]).  With [Set Crane Loopify], [dbl_e] becomes a frame-stack
    loop that inlines [dbl_md] as extra frames ([_Enter_inl]), but both halves
    store into the one [_result] variable, declared at [dbl_e]'s result type:
    [_result = Md::mnull();] assigns an [md] to an [e] -- "no viable
    overloaded '='" -- and the resume frame then hands that [_result] to a
    constructor expecting the other type.

    Found in Vellvm with the global [Set Crane Loopify]:
    [Traversal.ft_exp] / [ft_metadata], 4 of its 59 errors. *)

Module LoopifyMutualResultTypes.

  Inductive e := Leaf (n : nat) | Add (a b : e) | Meta (m : md)
  with md := MNull | MConst (x : e) | MPair (a b : md).

  Fixpoint dbl_e (x : e) : e :=
    match x with
    | Leaf n => Leaf (2 * n)
    | Add a b => Add (dbl_e a) (dbl_e b)
    | Meta m => Meta (dbl_md m)
    end
  with dbl_md (m : md) : md :=
    match m with
    | MNull => MNull
    | MConst x => MConst (dbl_e x)
    | MPair a b => MPair (dbl_md a) (dbl_md b)
    end.

  Fixpoint sum_e (x : e) : nat :=
    match x with
    | Leaf n => n
    | Add a b => sum_e a + sum_e b
    | Meta m => sum_md m
    end
  with sum_md (m : md) : nat :=
    match m with
    | MNull => 0
    | MConst x => sum_e x
    | MPair a b => sum_md a + sum_md b
    end.

  Definition sample : e :=
    Add (Leaf 1) (Meta (MPair (MConst (Add (Leaf 2) (Leaf 3))) (MPair MNull (MConst (Leaf 4))))).

  (** 2 * (1 + 2 + 3 + 4) *)
  Definition check (_ : unit) : bool := Nat.eqb (sum_e (dbl_e sample)) 20.

End LoopifyMutualResultTypes.

Set Crane Loopify.
Crane Extraction "loopify_mutual_result_types" LoopifyMutualResultTypes.
