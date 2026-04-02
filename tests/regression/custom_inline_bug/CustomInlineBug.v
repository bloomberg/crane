(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Custom inline extraction bugs: std::make_optional and std::make_pair *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

Module CustomInlineBug.

Record State : Type := mkState {
  value : nat;
  data : nat
}.

(* ===== FROM RealBug.v ===== *)
(* BUG TRIGGER: Some (projection of last-use variable)
   Without defensive fix, this generates:
     std::make_optional<unsigned int>(std::move(s)->value)
   Which is use-after-move - std::move(s) makes s null, then ->value segfaults!
   With defensive fix, generates:
     std::make_optional<unsigned int>(s->value)
   Which is safe.
*)
Definition bug_some_proj (s : State) : option nat :=
  Some (value s).

(* Variant: with pair (uses std::make_pair) *)
Definition bug_pair_proj (s : State) : State * nat :=
  pair s (value s).

(* Variant: nested option *)
Definition bug_nested_option (s : State) : option (option nat) :=
  Some (Some (value s)).

(* Variant: option of pair *)
Definition bug_option_pair (s : State) : option (State * nat) :=
  Some (pair s (value s)).

(* Variant: with function call result *)
Definition get_state (n : nat) : State := mkState n n.

Definition bug_some_of_call (n : nat) : option nat :=
  Some (value (get_state n)).

(* ===== FROM PairBug.v ===== *)
(* Pairs use std::make_pair (custom inline extraction), NOT factory methods *)

(* Test 1: Simplest case - pair with projection *)
Definition pair_simple (s : State) : State * nat :=
  (s, value s).

(* Test 2: Let-bound value used in pair with projection *)
Definition pair_let (n : nat) : State * nat :=
  let s := mkState n n in
  (s, value s).

(* Test 3: Nested pairs *)
Definition pair_nested (s : State) : (State * nat) * (nat * nat) :=
  ((s, value s), (value s, data s)).

(* Test 4: Pair in tail position of if *)
Definition pair_if (b : bool) (s : State) : State * nat :=
  if b then (s, value s) else (s, 0).

(* Test 5: Pair in both match branches *)
Definition pair_match (o : option State) : option (State * nat) :=
  match o with
  | Some s => Some (s, value s)
  | None => None
  end.

(* Test 6: Multiple projections in pair *)
Definition pair_multi_proj (s : State) : (State * nat) * nat :=
  ((s, value s), data s).

(* Test 7: Chain of lets ending in pair *)
Definition pair_chain (s1 : State) : State * nat :=
  let s2 := mkState (value s1) (data s1) in
  let s3 := mkState (value s2) (data s2) in
  (s3, value s3).

(* Test 8: Same value used 4 times via pairs *)
Definition pair_extreme (s : State) : (State * State) * (nat * nat) :=
  ((s, s), (value s, data s)).

(* Test 9: Nested function returning pair *)
Definition make_pair (s : State) : State * nat :=
  (s, value s).

Definition outer_pair (n : nat) : State * nat :=
  make_pair (mkState n n).

(* Test 10: Pair in fixpoint *)
Fixpoint count_pairs (n : nat) (s : State) : list (State * nat) :=
  match n with
  | O => nil
  | S m => cons (s, value s) (count_pairs m s)
  end.

End CustomInlineBug.

Crane Extraction "custom_inline_bug" CustomInlineBug.
