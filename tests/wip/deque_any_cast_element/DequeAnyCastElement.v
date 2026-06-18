From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

(* Reproduce: a function stored in a sigT whose type is erased to any->any.
   Inside the function body, it destructures a product and conses onto a list.
   Crane should cast the list component to deque<pair<uint64_t,uint64_t>>
   but generates any_cast<deque<any>> because the function type is erased. *)

Inductive tag := TagA | TagB.

Definition input_ty (t : tag) : Type :=
  match t with
  | TagA => nat * (list (nat * nat) * nat)
  | TagB => nat
  end.

Definition output_ty (t : tag) : Type :=
  match t with
  | TagA => list (nat * nat)
  | TagB => nat
  end.

Definition action_entry := { t : tag & (input_ty t -> output_ty t) }.

Definition my_action : action_entry :=
  existT _ TagA (fun tup =>
    let '(x, (xs, y)) := tup in
    (x, y) :: xs).

Definition apply_entry (e : action_entry) : { t : tag & output_ty t } :=
  match e with
  | existT _ TagA f => existT _ TagA (f (10, ((1, 2) :: (3, 4) :: nil, 20)))
  | existT _ TagB f => existT _ TagB (f 5)
  end.

Definition get_length (r : { t : tag & output_ty t }) : nat :=
  match r with
  | existT _ TagA ps => length ps
  | existT _ TagB n => n
  end.

Definition test_result : nat := get_length (apply_entry my_action).

Set Crane Extraction Output Directory "tests/wip/deque_any_cast_element".
Set Crane Loopify.
Crane Separate Extraction test_result.
