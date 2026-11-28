(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A [Global] store whose value type is chosen by the index: index [0]
    holds lists, every other index numbers.  At a known index the value
    type [V 0] reduces to [list X], so an array made there is an array of
    lists, whether [V] is a notation (a [match] in the type) or a global
    definition (unfolded first), and whether the element type is generic
    or concrete. *)

From Stdlib Require Import List.
From ITree Require Import Events.Exception ITree.
From Crane Require Monads.ST Monads.Global.
From Crane Require Import Mapping.NatInt Monads.Error Monads.Indices Monads.ITree.

Import Monads.
Import ListNotations.
Local Open Scope monad_scope.

Module GlobalIndexedValueType.

(** The value types as a global definition. *)
Definition VD (X : Type) (i : nat) : Type :=
  match i with
  | O => list X
  | S _ => X
  end.

Section Generic.

  Context {X : Type} {E : Type -> Type}.

  (** The value types as a notation: a [match] in the type. *)
  Notation VN := (fun i : nat => match i with O => list X | S _ => X end).

  (** [n] empty lists, the second then set to [[x; y]], read back. *)
  Definition lists_notation `{Global.Event nat VN -< E} (n : nat) (x y : X)
    : itree E (list (list X)) :=
    arr <- Global.new_array (V := VN) 0 n [];;
    Global.write_array (V := VN) (idx := 0) arr 1 [x; y];;
    Global.array_to_list (V := VN) arr.

  (** The same over the global definition. *)
  Definition lists_definition `{Global.Event nat (VD X) -< E} (n : nat) (x y : X)
    : itree E (list (list X)) :=
    arr <- Global.new_array (V := VD X) 0 n [];;
    Global.write_array (V := VD X) (idx := 0) arr 1 [x; y];;
    Global.array_to_list (V := VD X) arr.

  (** A reference at index [1] holds an [X]. *)
  Definition number_definition `{Global.Event nat (VD X) -< E} (x : X) : itree E X :=
    r <- Global.new_ref (V := VD X) 1 x;;
    Global.read_ref (V := VD X) (idx := 1) r.

End Generic.

(** At a concrete element type. *)
Definition lists_concrete (n : nat)
  : itree (Global.Event nat (VD nat) +' exceptE Err) (list (list nat)) :=
  arr <- Global.new_array (V := VD nat) 0 n [];;
  Global.write_array (V := VD nat) (idx := 0) arr 0 [7];;
  Global.array_to_list (V := VD nat) arr.

Definition via_notation (n : nat) :=
  @lists_notation nat (Global.Event nat (fun i => match i with O => list nat | S _ => nat end)
    +' exceptE Err) _ n 1 2.
Definition via_definition (n : nat) :=
  @lists_definition nat (Global.Event nat (VD nat) +' exceptE Err) _ n 3 4.
Definition number := @number_definition nat (Global.Event nat (VD nat) +' exceptE Err) _ 9.

End GlobalIndexedValueType.

Crane Extraction "global_indexed_value_type" GlobalIndexedValueType.
