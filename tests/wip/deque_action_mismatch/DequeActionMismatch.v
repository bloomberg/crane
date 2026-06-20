From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

(* Reproduces the JSON parser grammar action mismatch:
   - Multiple "actions" (type-erased functions) produce/consume the same
     list type (list (nat * nat)).
   - One action produces an empty list (base case).
   - Another action conses onto a list received as input.
   - A third action consumes the final list.

   The bug: the base case produces deque<pair<uint64_t,uint64_t>> (concrete),
   but the cons action casts its input to deque<any> — type mismatch at runtime. *)

Inductive tag := TagList | TagNat.

Definition sem_ty (t : tag) : Type :=
  match t with
  | TagList => list (nat * nat)
  | TagNat => nat
  end.

(* An "action" is a type-erased function, mimicking grammar_entry actions. *)
Definition action := { t : tag & (sem_ty t -> sem_ty t) }.

(* Base case action: ignores input, returns empty list.
   This will produce a concrete deque<pair<uint64_t,uint64_t>>{}. *)
Definition base_action : action :=
  existT _ TagList (fun _ => []).

(* Cons action: takes a list and conses a fixed element onto it.
   Inside the erased lambda, it must cast the input from any to deque<T>. *)
Definition cons_action : action :=
  existT _ TagList (fun xs => (42, 99) :: xs).

(* Apply an action to a value of matching tag *)
Definition apply_action (a : action) (v : { t : tag & sem_ty t })
  : { t : tag & sem_ty t } :=
  match a, v with
  | existT _ TagList f, existT _ TagList xs => existT _ TagList (f xs)
  | existT _ TagNat f, existT _ TagNat n => existT _ TagNat (f n)
  | _, _ => v
  end.

(* Chain: base produces [], then cons adds (42,99), then cons adds (42,99) again.
   The intermediate values pass through std::any boundaries. *)
Definition chain : { t : tag & sem_ty t } :=
  let v0 := existT _ TagList [] in
  let v1 := apply_action base_action v0 in
  let v2 := apply_action cons_action v1 in
  let v3 := apply_action cons_action v2 in
  v3.

Definition get_length (v : { t : tag & sem_ty t }) : nat :=
  match v with
  | existT _ TagList ps => length ps
  | existT _ TagNat _ => 0
  end.

Definition get_first (v : { t : tag & sem_ty t }) : nat :=
  match v with
  | existT _ TagList ((x, _) :: _) => x
  | _ => 0
  end.

Definition test_length : nat := get_length chain.
Definition test_first : nat := get_first chain.

Set Crane Extraction Output Directory "tests/wip/deque_action_mismatch".
Set Crane Loopify.
Crane Separate Extraction test_length test_first.
