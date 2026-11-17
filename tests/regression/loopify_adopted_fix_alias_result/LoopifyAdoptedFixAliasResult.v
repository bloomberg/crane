(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import List.
Import ListNotations.
Require Import Crane.Mapping.NatIntStd.
Require Crane.Extraction.

(** A machine adopting a local fixpoint that calls back into its function,
    the function's result written through a type abbreviation -- the shape
    of [FMapList.map2] and [combine].

    The function returns [t C]; extraction gives the fixpoint the unfolded
    [list (nat * C)], and the C++ spells the two [t<T3>] and
    [List<std::pair<uint64_t, T3>>].  The frame transform once told
    them apart by that spelling, dropped the adoption the plan had made,
    and left [map2] the recursion it is. *)
Module LoopifyAdoptedFixAliasResult.

Definition t (A : Type) : Type := list (nat * A).

Definition option_cons {A} (k : nat) (o : option A) (l : t A) : t A :=
  match o with Some e => (k, e) :: l | None => l end.

Section Elt.
Variables A B C : Type.
Variable f : option A -> option B -> option C.

Fixpoint map2_l (m : t A) : t C :=
  match m with
  | nil => nil
  | (k, e) :: l => option_cons k (f (Some e) None) (map2_l l)
  end.

Fixpoint map2_r (m : t B) : t C :=
  match m with
  | nil => nil
  | (k, e) :: l => option_cons k (f None (Some e)) (map2_r l)
  end.

Fixpoint map2 (m : t A) : t B -> t C :=
  match m with
  | nil => map2_r
  | (k, e) :: l =>
    fix map2_aux (m' : t B) : t C :=
      match m' with
      | nil => map2_l m
      | (k', e') :: l' =>
        if Nat.ltb k k' then option_cons k (f (Some e) None) (map2 l m')
        else if Nat.ltb k' k then option_cons k' (f None (Some e')) (map2_aux l')
        else option_cons k (f (Some e) (Some e')) (map2 l l')
      end
  end.
End Elt.

Definition add_opt (a b : option nat) : option nat :=
  match a, b with
  | Some x, Some y => Some (x + y)
  | Some x, None | None, Some x => Some x
  | None, None => None
  end.

Definition sum (m : t nat) : nat := fold_left (fun acc p => acc + snd p) m 0.

(** The keys [i * step], ..., [(i + n - 1) * step], each bound to its
    multiple. *)
Fixpoint keys (n i step : nat) : t nat :=
  match n with
  | O => nil
  | S n' => (i * step, i) :: keys n' (S i) step
  end.

Definition merged (n : nat) : t nat := map2 _ _ _ add_opt (keys n 0 2) (keys n 0 3).

End LoopifyAdoptedFixAliasResult.

Set Crane Loopify.
Crane Extraction "loopify_adopted_fix_alias_result" LoopifyAdoptedFixAliasResult.
