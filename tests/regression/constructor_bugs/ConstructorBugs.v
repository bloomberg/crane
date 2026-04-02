(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Constructor-specific use-after-move patterns *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
Require Import List.
Import ListNotations.

Module ConstructorBugs.

(* ===== FROM ExactPattern.v ===== *)
(* User's exact reported pattern *)

Record field_a : Type := mkFieldA {
  a_value : nat
}.

Record field_b : Type := mkFieldB {
  b_value : nat
}.

Record source_state : Type := mkSource {
  source_a : field_a;
  source_b : field_b;
  source_flag : nat
}.

Record packed_state : Type := mkPacked {
  packed_source : source_state;
  packed_a : field_a;
  packed_b : field_b
}.

Definition step (s : source_state) : source_state := s.

(* EXACT pattern from user's bug report *)
Definition bad_branch (s1 : source_state) : bool * packed_state :=
  let s2 := step s1 in
  if Nat.eqb (source_flag s2) 0 then
    (false, mkPacked s2 (source_a s2) (source_b s2))
  else
    (false, mkPacked s2 (source_a s2) (source_b s2)).

(* Variant: without if-expression *)
Definition bad_direct (s1 : source_state) : bool * packed_state :=
  let s2 := step s1 in
  (false, mkPacked s2 (source_a s2) (source_b s2)).

(* Variant: with more complex step function *)
Definition step2 (s : source_state) : source_state :=
  mkSource (source_a s) (source_b s) (source_flag s + 1).

Definition bad_complex_step (s1 : source_state) : bool * packed_state :=
  let s2 := step2 s1 in
  if Nat.eqb (source_flag s2) 0 then
    (false, mkPacked s2 (source_a s2) (source_b s2))
  else
    (false, mkPacked s2 (source_a s2) (source_b s2)).

(* Variant: nested lets *)
Definition bad_nested (s1 : source_state) : bool * packed_state :=
  let s2 := step s1 in
  let s3 := step s2 in
  (false, mkPacked s3 (source_a s3) (source_b s3)).

(* ===== FROM ExactUserBug.v ===== *)
(* Exact with list field *)

Record source_state_list : Type := mkSourceList {
  source_a_list : field_a;
  source_b_list : list field_b;
  source_flag_list : nat
}.

Record packed_state_list : Type := mkPackedList {
  packed_source_list : source_state_list;
  packed_a_list : field_a;
  packed_b_list : list field_b
}.

Definition step_list (s : source_state_list) : source_state_list := s.

(* EXACT code from user's bug report *)
Definition bad_branch_list (s1 : source_state_list) : bool * packed_state_list :=
  let s2 := step_list s1 in
  if Nat.eqb (source_flag_list s2) 0 then
    (false, mkPackedList s2 (source_a_list s2) (source_b_list s2))
  else
    (false, mkPackedList s2 (source_a_list s2) (source_b_list s2)).

(* ===== FROM SegfaultTest.v ===== *)
(* Aggressive test cases *)

Record state : Type := mkState {
  value : nat;
  data : list nat
}.

(* Helper that returns state by value *)
Definition get_state (n : nat) : state :=
  mkState n [n; n+1; n+2].

(* Test 1: Tuple with same element multiple times from function call *)
Definition tuple_from_call (n : nat) : state * state * nat :=
  let s := get_state n in
  (s, s, value s).

(* Test 2: Nested tuples with projections *)
Definition nested_tuples (s : state) : (state * nat) * (nat * list nat) :=
  ((s, value s), (value s, data s)).

(* Test 3: If-then-else in tail returning tuples *)
Definition conditional_tuple (b : bool) (n : nat) : state * nat * list nat :=
  let s := get_state n in
  if b then
    (s, value s, data s)
  else
    (s, value s, data s).

(* Test 4: Multiple levels of function calls *)
Definition extract_value (s : state) : nat := value s.
Definition extract_data (s : state) : list nat := data s.

Definition multi_call_tuple (n : nat) : state * nat * list nat :=
  let s := get_state n in
  (s, extract_value s, extract_data s).

(* Test 5: Pair (uses std::make_pair) *)
Definition pair_test (n : nat) : nat * (state * nat) :=
  let s := get_state n in
  (n, (s, value s)).

(* Test 6: Match with scrutinee reuse *)
Definition match_test (o : option state) : option (state * nat) :=
  match o with
  | Some s => Some (s, value s)
  | None => None
  end.

(* Test 7: List construction *)
Definition list_test (s : state) : list state :=
  s :: s :: [s].

(* Test 8: Triple nested projections *)
Definition triple_proj (s : state) : (state * nat) * (nat * list nat) * list nat :=
  ((s, value s), (value s, data s), data s).

(* Test 9: Return pair from function result *)
Definition inner_pair (s : state) : state * nat :=
  (s, value s).

Definition outer_call (n : nat) : state * nat :=
  inner_pair (get_state n).

(* Test 10: Extreme - same variable used 5 times *)
Definition extreme_reuse (s : state) : state * state * nat * nat * list nat :=
  (s, s, value s, value s, data s).

(* ===== FROM EdgeCases.v ===== *)
(* Edge cases that might bypass escape analysis *)

Record Inner : Type := mkInner {
  inner_val : nat
}.

Record Outer : Type := mkOuter {
  outer_inner : Inner;
  outer_data : nat
}.

(* Case 1: Nested record construction - record inside record *)
Definition nested_record (i : Inner) : Outer :=
  mkOuter i (inner_val i).

(* Case 2: Record construction where one field IS another field's projection *)
Definition self_referential (o : Outer) : Outer :=
  mkOuter (outer_inner o) (inner_val (outer_inner o)).

(* Case 3: std::make_pair with projections *)
Definition pair_with_proj (i : Inner) : Inner * nat :=
  (i, inner_val i).

(* Case 4: Nested pairs with same source *)
Definition nested_pairs (i : Inner) : (Inner * nat) * (nat * nat) :=
  ((i, inner_val i), (inner_val i, inner_val i)).

(* Case 5: Pair where both elements are the same variable *)
Definition pair_duplicate (i : Inner) : Inner * Inner :=
  (i, i).

(* Case 6: Function returning Inner by value, used in pair *)
Definition mk_inner (n : nat) : Inner := mkInner n.

Definition pair_from_func (n : nat) : Inner * nat :=
  let i := mk_inner n in
  (i, inner_val i).

(* Case 7: Match on option, construct record in Some branch *)
Definition match_option_record (o : option Inner) : option (Inner * nat) :=
  match o with
  | Some i => Some (i, inner_val i)
  | None => None
  end.

(* Case 8: Match on sum type *)
Inductive MySum : Type :=
  | Left : Inner -> MySum
  | Right : nat -> MySum.

Definition match_sum (s : MySum) : Inner * nat :=
  match s with
  | Left i => (i, inner_val i)
  | Right n => (mkInner n, n)
  end.

(* Case 9: Let with magic cast (type coercion) *)
Definition with_cast (i : Inner) : Inner * nat :=
  let x : Inner := i in
  (x, inner_val x).

(* Case 10: Multiple let bindings, each used multiple times *)
Definition chain_lets (i1 : Inner) : (Inner * nat) * (Inner * nat) :=
  let i2 := mkInner (inner_val i1) in
  let i3 := mkInner (inner_val i2) in
  ((i2, inner_val i2), (i3, inner_val i3)).

(* Case 11: Projection chain *)
Record Container : Type := mkContainer {
  cont_outer : Outer
}.

Definition deep_proj (c : Container) : Outer * Inner * nat :=
  let o := cont_outer c in
  let i := outer_inner o in
  (o, i, inner_val i).

(* Case 12: List with projections *)
Definition list_with_proj (i : Inner) : list Inner * nat :=
  ([i; i; i], inner_val i).

(* Case 13: Pair in tail of function returning pair *)
Definition tail_pair (i : Inner) (b : bool) : Inner * nat :=
  if b then (i, inner_val i) else (i, 0).

(* Case 14: Tuple with 4 elements all derived from same source *)
Definition quad_tuple (i : Inner) : (Inner * Inner) * (nat * nat) :=
  ((i, i), (inner_val i, inner_val i)).

(* Case 15: Pair constructed in both branches of match *)
Definition match_both_branches (o : option Inner) : (option Inner) * nat :=
  match o with
  | Some i => (Some i, inner_val i)
  | None => (None, 0)
  end.

(* Case 16: Sigma type (dependent pair) with projection *)
Definition sigma_test (i : Inner) : {x : Inner | inner_val x = inner_val i} :=
  exist _ i eq_refl.

(* Case 17: Nested function calls with projections *)
Definition extract (i : Inner) : nat := inner_val i.

Definition nested_extract (i : Inner) : Inner * nat :=
  (i, extract i).

(* Case 18: Record update syntax *)
Definition update_test (o : Outer) : Outer * nat :=
  (mkOuter (outer_inner o) (outer_data o + 1), inner_val (outer_inner o)).

(* ===== FROM InlineProjections.v ===== *)
(* NO let bindings - all projections inline in constructor arguments *)

Record State : Type := mkStateInline {
  value_inline : nat;
  data_inline : nat;
  flag : nat
}.

(* NO let - projections directly in pair *)
Definition inline_pair (s : State) : State * nat :=
  (s, value_inline s).

(* NO let - multiple inline projections *)
Definition inline_triple (s : State) : State * nat * nat :=
  (s, value_inline s, data_inline s).

(* NO let - nested pair with inline projections *)
Definition inline_nested (s : State) : (State * nat) * nat :=
  ((s, value_inline s), data_inline s).

(* NO let - function call result with inline projection *)
Definition get_state_inline (n : nat) : State := mkStateInline n n n.

Definition inline_from_call (n : nat) : State * nat :=
  (get_state_inline n, value_inline (get_state_inline n)).

(* CRITICAL: Same function call, multiple projections *)
Definition same_call_multi_proj (n : nat) : State * nat * nat :=
  (get_state_inline n, value_inline (get_state_inline n), data_inline (get_state_inline n)).

(* NO let - match result with inline projection *)
Definition inline_match (o : option State) : option (State * nat) :=
  match o with
  | Some s => Some (s, value_inline s)
  | None => None
  end.

(* NO let - if result with inline projection *)
Definition inline_if (b : bool) (s : State) : State * nat :=
  if b then (s, value_inline s) else (s, 0).

(* NO let - nested projections inline *)
Record OuterInline : Type := mkOuterInline {
  outer_state : State;
  outer_num : nat
}.

Definition inline_deep (o : OuterInline) : OuterInline * State * nat :=
  (o, outer_state o, value_inline (outer_state o)).

(* NO let - projection of projection inline *)
Definition inline_double_proj (o : OuterInline) : State * nat :=
  (outer_state o, value_inline (outer_state o)).

(* NO let - same source, many inline projections *)
Definition inline_many (s : State) : (State * nat) * (nat * nat) :=
  ((s, value_inline s), (data_inline s, flag s)).

(* NO let - pattern match with inline projections *)
Definition inline_pattern (s : State) : nat * State * nat :=
  match s with
  | mkStateInline v d f => (v, s, d)
  end.

(* NO let - pair constructor in recursive call *)
Fixpoint inline_recursive (n : nat) (s : State) : list (State * nat) :=
  match n with
  | O => nil
  | Datatypes.S m => (s, value_inline s) :: inline_recursive m s
  end.

(* NO let - complex nested expression *)
Definition inline_complex (s : State) : ((State * nat) * nat) * (nat * State) :=
  (((s, value_inline s), data_inline s), (flag s, s)).

(* NO let - multiple uses in one constructor, no intermediate variables *)
Definition inline_quad (s : State) : (State * State) * (nat * nat) :=
  ((s, s), (value_inline s, data_inline s)).

(* NO let - projection in both branches, no let binding *)
Definition inline_both_branches (b : bool) (s : State) : State * nat :=
  if b then (s, value_inline s) else (s, value_inline s).

(* SUPER CRITICAL: Application result used multiple times inline *)
Definition apply_twice (f : State -> nat) (s : State) : State * nat * nat :=
  (s, f s, f s).

Definition test_apply (s : State) : State * nat * nat :=
  apply_twice value_inline s.

(* NO let - nested function calls with projections *)
Definition get_value_inline (s : State) : nat := value_inline s.
Definition get_data_inline (s : State) : nat := data_inline s.

Definition inline_nested_calls (s : State) : State * nat * nat :=
  (s, get_value_inline s, get_data_inline s).

(* NO let - option constructor with inline projections *)
Definition inline_option (s : State) : option State * option nat :=
  (Some s, Some (value_inline s)).

(* NO let - list constructor with inline projections *)
Definition inline_list (s : State) : list State * list nat :=
  (cons s nil, cons (value_inline s) nil).

End ConstructorBugs.

Crane Extraction "constructor_bugs" ConstructorBugs.
