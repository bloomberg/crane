(** WIP test: any_cast<deque<any>> when element type is concrete.
    Reproduces a crash in parse-a-lot's JSON grammar actions.

    Pattern: a sigT value where the dependent type is `list T`.
    When the value is extracted (projT2), Crane should generate
    any_cast<deque<T>> but may generate any_cast<deque<any>>.

    Also tests the dual bug: when the dependent type is just T (not a list),
    Crane may omit the any_cast entirely and use the std::any directly. *)
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.DequeList.
Require Crane.Extraction.

Module DequeElementCast.

Inductive val := VNum (n : nat) | VStr (s : nat).
Inductive nonterm := NT_ITEM | NT_ITEMS.

Definition sem_ty (nt : nonterm) : Type :=
  match nt with
  | NT_ITEM => val
  | NT_ITEMS => list val
  end.

Definition grammar_entry := { nt : nonterm & sem_ty nt }.

Definition items_value : grammar_entry :=
  existT _ NT_ITEMS [VNum 42; VStr 7; VNum 3].

Definition item_value : grammar_entry :=
  existT _ NT_ITEM (VNum 99).

(** Process only the ITEMS case to isolate the deque<any> bug *)
Definition count_items (e : grammar_entry) : nat :=
  match e with
  | existT _ NT_ITEMS vs => length vs
  | existT _ NT_ITEM _ => 0
  end.

(** Process the ITEM case to test the missing any_cast bug *)
Definition get_item_num (e : grammar_entry) : nat :=
  match e with
  | existT _ NT_ITEMS _ => 0
  | existT _ NT_ITEM v =>
    match v with
    | VNum x => x
    | VStr x => x + 100
    end
  end.

Definition my_entries : list grammar_entry := [items_value; item_value].

Definition test_count : nat := count_items items_value.
Definition test_item_num : nat := get_item_num item_value.

End DequeElementCast.

Set Crane Loopify.
Crane Separate Extraction
  DequeElementCast.test_count
  DequeElementCast.test_item_num.
