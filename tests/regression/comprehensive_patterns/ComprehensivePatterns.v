(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Comprehensive use-after-move test patterns *)

From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.
Require Import List.
Import ListNotations.

Set Crane Loopify.  (* For LoopifyBug patterns *)

Module ComprehensivePatterns.

(* ===== FROM Aggressive.v ===== *)

Record S : Type := mkS {
  s_a : nat;
  s_b : nat;
  s_c : nat
}.

(* Pattern 1: Variable appears in constructor via different syntactic forms *)
Definition syntactic_variation (s : S) : S * nat * nat :=
  let a := s_a s in
  let b := s_b in  (* partially applied projection *)
  (s, a, b s).

(* Pattern 2: MLmagic (type cast) might hide occurrences? *)
Definition with_magic (s : S) : S * nat :=
  (s, s_a s).

(* Pattern 3: Deeply nested - 5 records deep *)
Record L1 : Type := mkL1 { l1_s : S }.
Record L2 : Type := mkL2 { l2_l1 : L1 }.
Record L3 : Type := mkL3 { l3_l2 : L2 }.
Record L4 : Type := mkL4 { l4_l3 : L3 }.
Record L5 : Type := mkL5 { l5_l4 : L4 }.

Definition deep_nest (l5 : L5) : L5 * L4 * L3 * L2 * L1 * S * nat :=
  let l4 := l5_l4 l5 in
  let l3 := l4_l3 l4 in
  let l2 := l3_l2 l3 in
  let l1 := l2_l1 l2 in
  let s := l1_s l1 in
  (l5, l4, l3, l2, l1, s, s_a s).

(* Pattern 4: Same value used in nested pairs *)
Definition nested_pair_reuse (s : S) : ((S * nat) * nat) * nat :=
  (((s, s_a s), s_b s), s_c s).

(* Pattern 5: Function composition with projections *)
Definition compose (s : S) : S * nat :=
  let f := fun x => s_a x in
  (s, f s).

(* Pattern 6: Projection inside lambda *)
Definition lambda_proj (s : S) : (nat -> nat) * S :=
  (fun _ => s_a s, s).

(* Pattern 7: Let chain where each step projects previous *)
Definition proj_chain (s : S) : S * nat * nat * nat :=
  let x := s in
  let a := s_a x in
  let b := s_b x in
  let c := s_c x in
  (x, a, b, c).

(* Pattern 8: Tuple with 8 elements all from same source *)
Definition octuple (s : S) : (((S * S) * (nat * nat)) * ((nat * nat) * (nat * nat))) :=
  (((s, s), (s_a s, s_b s)), ((s_c s, s_a s), (s_b s, s_c s))).

(* Pattern 9: Pair inside option inside pair *)
Definition nested_containers (s : S) : option (S * nat) * S :=
  (Some (s, s_a s), s).

(* Pattern 10: Match on pair, use both components *)
Definition match_pair (p : S * nat) : S * nat * nat :=
  match p with
  | (s, n) => (s, n, s_a s)
  end.

(* Pattern 11: Recursive function that packs value with projection *)
Fixpoint make_list (n : nat) (s : ComprehensivePatterns.S) : list (ComprehensivePatterns.S * nat) :=
  match n with
  | O => nil
  | Datatypes.S m => cons (s, s_a s) (make_list m s)
  end.

(* Pattern 12: Multiple matches, same variable *)
Definition multi_match (o1 o2 : option S) : option (S * S) :=
  match o1 with
  | Some s1 =>
      match o2 with
      | Some s2 => Some (s1, s1)  (* s1 used twice *)
      | None => Some (s1, s1)
      end
  | None => None
  end.

(* Pattern 13: Pair constructor in tail of multi-branch match *)
Inductive Three := A | B | C.

Definition match_three (t : Three) (s : S) : S * nat :=
  match t with
  | A => (s, s_a s)
  | B => (s, s_b s)
  | C => (s, s_c s)
  end.

(* Pattern 14: Let binding in constructor argument *)
Definition let_in_arg (s : S) : S * nat :=
  (s, let x := s in s_a x).

(* Pattern 15: Projection via pattern match *)
Definition match_record (s : S) : S * nat :=
  match s with
  | mkS a b c => (s, a)
  end.

(* Pattern 16: Same variable bound multiple times via let *)
Definition rebind (s1 : S) : S * nat :=
  let s2 := s1 in
  let s3 := s2 in
  let s4 := s3 in
  (s4, s_a s4).

(* Pattern 17: Pair of functions that close over same variable *)
Definition closure_pair (s : S) : (unit -> nat) * (unit -> nat) :=
  (fun _ => s_a s, fun _ => s_b s).

(* Pattern 18: Existential/sigma where witness is used in proof *)
Definition sigma_reuse (s : S) : {x : S | s_a x = s_a s} :=
  exist _ s eq_refl.

(* Pattern 19: Multiple projections in one argument position *)
Definition multi_proj_arg (s : S) : nat * (nat * nat) :=
  (s_a s, (s_a s, s_b s)).

(* Pattern 20: Value and its projection both in same sum type *)
Inductive Either := Left_S (s : S) | Right_N (n : nat).

Definition both_in_sum (s : S) : Either * Either :=
  (Left_S s, Right_N (s_a s)).

(* ===== FROM HarderTests.v ===== *)

Record R1 : Type := mkR1 {
  r1_val : nat
}.

Record R2 : Type := mkR2 {
  r2_inner : R1;
  r2_data : nat
}.

Record R3 : Type := mkR3 {
  r3_r2 : R2;
  r3_r1 : R1;
  r3_num : nat
}.

(* Case 1: Projection chain - s used directly AND via projections *)
Definition hard_proj_chain (r3 : R3) : R3 * R2 * R1 * nat :=
  let r2 := r3_r2 r3 in
  let r1 := r2_inner r2 in
  (r3, r2, r1, r1_val r1).

(* Case 2: Same value accessed through different projection paths *)
Definition multi_path (r3 : R3) : R2 * R1 * nat :=
  (r3_r2 r3, r2_inner (r3_r2 r3), r1_val (r2_inner (r3_r2 r3))).

(* Case 3: Let bindings with projections, then use in constructor *)
Definition let_proj (r2 : R2) : R2 * R1 * nat :=
  let r1 := r2_inner r2 in
  let n := r1_val r1 in
  (r2, r1, n).

(* Case 4: Projection inside function call that's inside constructor *)
Definition extract_val (r1 : R1) : nat := r1_val r1.

Definition nested_call (r2 : R2) : R2 * nat :=
  (r2, extract_val (r2_inner r2)).

(* Case 5: Multiple projections on let-bound variable *)
Definition multi_proj_let (n : nat) : R2 * R1 * nat :=
  let r2 := mkR2 (mkR1 n) n in
  (r2, r2_inner r2, r2_data r2).

(* Case 6: Projection in match scrutinee AND in branch *)
Definition match_proj (r2 : R2) : option (R2 * R1) :=
  match Some (r2_inner r2) with
  | Some r1 => Some (r2, r1)
  | None => None
  end.

(* Case 7: Projection result used multiple times *)
Definition proj_multi_use (r2 : R2) : R1 * nat * nat :=
  let r1 := r2_inner r2 in
  (r1, r1_val r1, r1_val r1).

(* Case 8: Complex nesting - value used at multiple levels *)
Definition complex_nest (r3 : R3) : (R3 * R2) * (R1 * nat) :=
  ((r3, r3_r2 r3), (r2_inner (r3_r2 r3), r1_val (r2_inner (r3_r2 r3)))).

(* Case 9: Function returning record, used with projections *)
Definition make_r2 (n : nat) : R2 := mkR2 (mkR1 n) n.

Definition from_func (n : nat) : R2 * R1 * nat :=
  let r2 := make_r2 n in
  (r2, r2_inner r2, r2_data r2).

(* Case 10: Pair of pairs with projections *)
Definition pair_of_pairs (r2 : R2) : (R2 * R1) * (R1 * nat) :=
  let r1 := r2_inner r2 in
  ((r2, r1), (r1, r1_val r1)).

(* Case 11: Conditional with projections in both branches *)
Definition cond_proj (b : bool) (r2 : R2) : R2 * R1 :=
  if b then
    (r2, r2_inner r2)
  else
    (r2, r2_inner r2).

(* Case 12: Fixpoint with record parameter *)
Fixpoint repeat_r2 (n : nat) (r2 : R2) : list (R2 * R1) :=
  match n with
  | O => nil
  | Datatypes.S m => cons (r2, r2_inner r2) (repeat_r2 m r2)
  end.

(* Case 13: Nested let bindings, each used in final constructor *)
Definition nested_lets (r3 : R3) : R3 * R2 * R1 :=
  let r2 := r3_r2 r3 in
  let r1 := r2_inner r2 in
  (r3, r2, r1).

(* Case 14: Projection on projection result *)
Definition double_proj (r3 : R3) : R1 * nat :=
  (r2_inner (r3_r2 r3), r1_val (r2_inner (r3_r2 r3))).

(* Case 15: Same record accessed via variable AND projection *)
Definition mixed_access (r3 : R3) : R3 * R2 * R2 :=
  let r2 := r3_r2 r3 in
  (r3, r2, r3_r2 r3).

(* Case 16: Projection in tuple construction, returned from function *)
Definition return_proj_h (r2 : R2) : R2 * R1 :=
  (r2, r2_inner r2).

(* Case 17: Deep nesting with all levels used *)
Definition all_levels (r3 : R3) : R3 * R2 * R1 * nat :=
  (r3, r3_r2 r3, r2_inner (r3_r2 r3), r1_val (r2_inner (r3_r2 r3))).

(* Case 18: Let with projection, projection used again *)
Definition let_and_proj (r2 : R2) : R1 * R1 :=
  let r1 := r2_inner r2 in
  (r1, r2_inner r2).

(* Case 19: Multiple records constructed from same source *)
Definition multi_construct (r1 : R1) : R2 * R2 :=
  let r2a := mkR2 r1 0 in
  let r2b := mkR2 r1 1 in
  (r2a, r2b).

(* Case 20: Projection through option *)
Definition option_proj (o : option R2) : option (R2 * R1) :=
  match o with
  | Some r2 => Some (r2, r2_inner r2)
  | None => None
  end.

(* ===== FROM Pathological.v ===== *)

Record R : Type := mkR {
  val : nat;
  dat : nat
}.

(* CRITICAL: Pair constructor with inline projections *)
Definition pair_inline_proj (r : R) : R * nat :=
  pair r (val r).

(* CRITICAL: Nested pairs with inline projections *)
Definition nested_pair_inline (r : R) : (R * nat) * nat :=
  pair (pair r (val r)) (dat r).

(* CRITICAL: Pattern match that binds AND uses base *)
Definition match_bind_and_use (r : R) : nat :=
  match r with
  | mkR v d => v + d + val r
  end.

(* CRITICAL: Let with type annotation *)
Definition let_with_type (r : R) : nat :=
  let x : R := r in
  val x + val r.

(* CRITICAL: Projection of let-bound value that's last use *)
Definition proj_of_last_use (r1 : R) : nat :=
  let r2 := r1 in
  val r2.

(* CRITICAL: Multiple let bindings of same value *)
Definition multi_let_same (r : R) : nat :=
  let x := r in
  let y := x in
  let z := y in
  val z + val y + val x.

(* CRITICAL: Option unwrap with projection *)
Definition option_unwrap_proj (o : option R) : nat :=
  match o with
  | Some r => val r + dat r
  | None => 0
  end.

(* CRITICAL: Pair where first element is function result, second is projection *)
Definition fun_result_and_proj (n : nat) : R * nat :=
  let r := mkR n n in
  pair r (val r).

(* CRITICAL: Same value bound in match, used multiple ways *)
Definition match_multi_use (o : option R) : option nat :=
  match o with
  | Some r => Some (val r + dat r)
  | None => None
  end.

(* CRITICAL: Projection in tuple *)
Definition tuple_proj (r : R) : R * nat * nat :=
  (r, val r, dat r).

(* CRITICAL: Let chain ending in pair *)
Definition chain_to_pair (r1 : R) : R * nat :=
  let r2 := r1 in
  let r3 := r2 in
  pair r3 (val r3).

(* CRITICAL: Fixpoint with pair in return *)
Fixpoint repeat_pair (n : nat) (r : R) : list (R * nat) :=
  match n with
  | O => nil
  | Datatypes.S m => pair r (val r) :: repeat_pair m r
  end.

(* CRITICAL: Pair construction in both branches *)
Definition cond_pair (b : bool) (r : R) : R * nat :=
  if b then pair r (val r) else pair r (dat r).

(* CRITICAL: Nested match with projections *)
Definition nested_match (o1 o2 : option R) : nat :=
  match o1 with
  | Some r1 =>
      match o2 with
      | Some r2 => val r1 + val r2
      | None => val r1
      end
  | None => 0
  end.

(* CRITICAL: Pair where both elements are projections *)
Definition both_proj (r : R) : nat * nat :=
  pair (val r) (dat r).

(* CRITICAL: Function composition with projections *)
Definition compose_proj (r : R) : nat :=
  let f := fun x => val x in
  let g := fun x => dat x in
  f r + g r.

(* CRITICAL: Projection through option *)
Definition proj_through_option (r : R) : option nat :=
  Some (val r).

(* ===== FROM NonConstructor.v ===== *)

Record NC : Type := mkNC {
  nc_a : nat;
  nc_b : nat;
  nc_c : nat
}.

(* CRITICAL: Projection as function argument *)
Definition use_proj (n : nat) : nat := n.

Definition proj_as_arg (r : NC) : nat :=
  use_proj (nc_a r).

(* CRITICAL: Multiple projections as different function arguments *)
Definition use_two (x y : nat) : nat := x + y.

Definition multi_proj_args (r : NC) : nat :=
  use_two (nc_a r) (nc_b r).

(* CRITICAL: Projection in let, then use base *)
Definition let_proj_then_base (r : NC) : nat :=
  let x := nc_a r in
  let y := nc_b r in
  x + y.

(* CRITICAL: Base in let, then multiple projections *)
Definition base_then_multi_proj (r : NC) : nat :=
  let r2 := r in
  (nc_a r2) + (nc_b r2) + (nc_c r2).

(* CRITICAL: Projection in if condition *)
Definition proj_in_condition (r : NC) : nat :=
  if Nat.eqb (nc_a r) 0 then nc_b r else nc_c r.

(* CRITICAL: Projection in match scrutinee *)
Definition proj_in_scrutinee (r : NC) : nat :=
  match nc_a r with
  | O => nc_b r
  | Datatypes.S n => n + nc_c r
  end.

(* CRITICAL: Function returning projection *)
Definition return_proj_nc (r : NC) : nat := nc_a r.

Definition call_return_proj (r : NC) : nat :=
  return_proj_nc r + nc_b r.

(* CRITICAL: Nested function calls with projections *)
Definition inc (n : nat) : nat := n + 1.

Definition nested_proj_calls (r : NC) : nat :=
  inc (nc_a r) + inc (nc_b r).

(* CRITICAL: Projection in recursive call *)
Fixpoint count_down (n : nat) (r : NC) : nat :=
  match n with
  | O => nc_a r
  | Datatypes.S m => count_down m r + nc_b r
  end.

(* CRITICAL: Same record passed to multiple functions *)
Definition f1 (r : NC) : nat := nc_a r.
Definition f2 (r : NC) : nat := nc_b r.

Definition multi_function_calls (r : NC) : nat :=
  f1 r + f2 r.

(* CRITICAL: Projection then pattern match on base *)
Definition proj_then_match (r : NC) : nat :=
  let x := nc_a r in
  match r with
  | mkNC _ b _ => x + b
  end.

(* CRITICAL: Let binding with projection used multiple times *)
Definition let_used_twice (r : NC) : nat :=
  let x := nc_a r in
  x + x.

(* CRITICAL: Base value used in function call and projection *)
Definition base_in_call_and_proj (r : NC) : bool :=
  Nat.eqb (nc_a r) (nc_a r).

(* CRITICAL: Chained lets with same base *)
Definition chained_lets_same_base (r : NC) : nat :=
  let x := nc_a r in
  let y := nc_b r in
  let z := nc_c r in
  x + y + z.

(* CRITICAL: Projection inside projection *)
Record OuterNC : Type := mkOuterNC {
  outer_nc : NC
}.

Definition double_proj_nc (o : OuterNC) : nat :=
  nc_a (outer_nc o) + nc_b (outer_nc o).

(* CRITICAL: Base used in multiple expression positions *)
Definition multi_positions (r : NC) : nat :=
  (nc_a r) + (if Nat.eqb (nc_b r) 0 then nc_a r else nc_c r).

(* CRITICAL: Projection in fold/reduce *)
Fixpoint sum_proj (n : nat) (r : NC) : nat :=
  match n with
  | O => 0
  | Datatypes.S m => nc_a r + sum_proj m r
  end.

(* CRITICAL: Base passed to higher-order function *)
Definition apply (f : NC -> nat) (r : NC) : nat := f r.

Definition hof_test (r : NC) : nat :=
  apply (fun x => nc_a x + nc_b x) r.

(* ===== FROM FunctionCalls.v ===== *)

Record State : Type := mkState {
  state_value : nat;
  state_data : nat
}.

Definition use_two_fc (x y : nat) : nat := x + y.

Definition bug_two_args (s : State) : nat :=
  use_two_fc (state_value s) (state_data s).

(* Variant: three arguments *)
Definition use_three (x y z : nat) : nat := x + y + z.

Definition bug_three_args (s : State) : nat :=
  use_three (state_value s) (state_data s) (state_value s).

(* Variant: argument is the whole record AND a projection *)
Definition take_state_and_val (s : State) (n : nat) : nat := n.

Definition bug_state_and_proj (s : State) : nat :=
  take_state_and_val s (state_value s).

(* Variant: nested function calls *)
Definition inner_func (n : nat) : nat := n + 1.

Definition bug_nested_calls (s : State) : nat :=
  use_two_fc (inner_func (state_value s)) (inner_func (state_data s)).

(* Variant: function call with projection in if condition *)
Definition bug_in_condition (s : State) : nat :=
  if Nat.eqb (state_value s) 0 then state_data s else state_value s.

(* Variant: Let-bound, then used in multiple function calls *)
Definition f1_fc (n : nat) : nat := n.
Definition f2_fc (n : nat) : nat := n + 1.

Definition bug_multi_calls (s : State) : nat :=
  let v := state_value s in
  f1_fc v + f2_fc v.

(* CRITICAL: Same base in multiple args, one is projection *)
Definition bug_base_and_proj (s : State) : State * nat :=
  let consume := fun (x : State) => x in
  let s2 := consume s in
  (s2, state_value s2).

(* ===== FROM LetBindings.v ===== *)

Definition sequential_lets (s : State) : nat :=
  let x := s in
  let y := state_value s in
  y.

(* Variant: Let then use base in next expression *)
Definition let_then_use_base (s : State) : State * nat :=
  let v := state_value s in
  (s, v).

(* Variant: Two projections in sequence *)
Definition two_proj_sequence (s : State) : nat :=
  let v := state_value s in
  let d := state_data s in
  v + d.

Definition let_multi_proj (s : State) : nat :=
  let v := state_value s in
  let d := state_data s in
  let sum := v + d in
  sum.

(* Variant: Nested lets with same base *)
Definition nested_lets_same_base (s : State) : nat :=
  let s2 := s in
  let v := state_value s2 in
  let d := state_data s2 in
  v + d.

Definition if_with_proj (s : State) : nat :=
  if Nat.eqb (state_value s) 0 then
    state_data s
  else
    state_value s.

(* Variant: Match as scrutinee, base used in branch *)
Definition match_scrutinee_proj (s : State) : nat :=
  match state_value s with
  | O => state_data s
  | Datatypes.S n => n
  end.

(* BUG TRIGGER: Projection result bound, base used later *)
Definition bind_proj_use_base (s : State) : State * nat :=
  let v := state_value s in
  (s, v).

(* ===== FROM Sequences.v ===== *)

Record RSeq : Type := mkRSeq { seq_val : nat }.

Definition side_effect (r : RSeq) : RSeq := r.

Definition after_side_effect (r : RSeq) : nat :=
  let r2 := side_effect r in
  let v := seq_val r2 in
  v.

(* Variant: Two side effects in sequence *)
Definition two_side_effects (r : RSeq) : nat :=
  let r2 := side_effect r in
  let r3 := side_effect r2 in
  seq_val r3.

(* Variant: Side effect in branch *)
Definition side_effect_in_branch (b : bool) (r : RSeq) : nat :=
  let r2 := if b then side_effect r else r in
  seq_val r2.

(* ===== FROM Statements.v ===== *)

Record StateStmt : Type := mkStateStmt {
  stmt_value : nat;
  stmt_data : nat
}.

Definition return_proj_stmt (s : StateStmt) : nat :=
  stmt_value s.

(* Variant: Complex return expression *)
Definition return_complex (s : StateStmt) : nat :=
  (stmt_value s) + (stmt_data s).

(* Variant: Return pair with projections *)
Definition return_pair (s : StateStmt) : nat * nat :=
  (stmt_value s, stmt_data s).

Record InnerStmt : Type := mkInnerStmt {
  inner_stmt_val : nat
}.

Record OuterStmt : Type := mkOuterStmt {
  outer_stmt_inner : InnerStmt;
  outer_stmt_data : nat
}.

Definition chained_proj (o : OuterStmt) : nat :=
  inner_stmt_val (outer_stmt_inner o).

(* Variant: Multiple levels *)
Record Level3Stmt : Type := mkLevel3Stmt {
  l3_outer_stmt : OuterStmt
}.

Definition triple_chain (l3 : Level3Stmt) : nat :=
  inner_stmt_val (outer_stmt_inner (l3_outer_stmt l3)).

Definition proj_in_arith (s : StateStmt) : nat :=
  (stmt_value s) + 10.

(* Variant: Multiple projections in same expression *)
Definition multi_proj_expr (s : StateStmt) : nat :=
  (stmt_value s) + (stmt_data s) * 2.

Definition proj_in_list (s : StateStmt) : list nat :=
  [stmt_value s; stmt_data s].

Definition compare_projs (s : StateStmt) : bool :=
  Nat.eqb (stmt_value s) (stmt_data s).

(* BUG TRIGGER: Negation/boolean ops with projection *)
Definition bool_with_proj (s : StateStmt) : bool :=
  negb (Nat.eqb (stmt_value s) 0).

(* BUG TRIGGER: Projection in recursive call *)
Fixpoint sum_values (n : nat) (s : StateStmt) : nat :=
  match n with
  | O => 0
  | Datatypes.S m => (stmt_value s) + sum_values m s
  end.

(* ===== FROM ControlFlow.v ===== *)

Record RCF : Type := mkRCF { cf_val : nat }.

Definition branch_use (b : bool) (r : RCF) : nat :=
  if b then cf_val r else cf_val r.

(* Variant: Different uses in branches *)
Definition branch_different (b : bool) (r : RCF) : RCF * nat :=
  if b then (r, cf_val r) else (r, 0).

Definition match_with_wild (o : option RCF) : nat :=
  match o with
  | Some r => cf_val r
  | _ => 0
  end.

Fixpoint sum_with_state (n : nat) (r : RCF) : nat :=
  match n with
  | O => cf_val r
  | Datatypes.S m => cf_val r + sum_with_state m r
  end.

(* Variant: Mutual recursion *)
Fixpoint even_count (n : nat) (r : RCF) : nat :=
  match n with
  | O => 0
  | Datatypes.S m => 1 + odd_count m r
  end
with odd_count (n : nat) (r : RCF) : nat :=
  match n with
  | O => cf_val r
  | Datatypes.S m => 1 + even_count m r
  end.

(* ===== FROM LoopifyBug.v ===== *)

Record StateLB : Type := mkStateLB {
  lb_value : nat;
  lb_data : nat
}.

Inductive Tree : Type :=
  | Leaf : nat -> Tree
  | Node : Tree -> nat -> Tree -> Tree.

Fixpoint tree_sum (t : Tree) : nat :=
  match t with
  | Leaf n => n
  | Node l v r => v + tree_sum l + tree_sum r
  end.

(* Variant: With record parameter *)
Fixpoint consume_tree_with_state (t : Tree) (s : StateLB) : nat :=
  match t with
  | Leaf n => n + lb_value s
  | Node l v r => v + lb_value s + consume_tree_with_state l s + consume_tree_with_state r s
  end.

(* Variant: Accum with projection *)
Fixpoint accum_with_state (n : nat) (s : StateLB) : nat :=
  match n with
  | O => lb_value s
  | Datatypes.S m => lb_value s + accum_with_state m s
  end.

(* ===== FROM ReuseOpt.v ===== *)

Definition transform_tree (t : Tree) : Tree :=
  match t with
  | Leaf n => Leaf (n + 1)
  | Node l v r => Node l (v + 1) r
  end.

(* Variant: Match that returns different constructor *)
Definition flip_tree (t : Tree) : Tree :=
  match t with
  | Leaf n => Node t n t
  | Node l v r => Leaf v
  end.

(* Variant: Match with multiple projections *)
Record StateRO : Type := mkStateRO {
  ro_value : nat;
  ro_data : nat
}.

Inductive Container : Type :=
  | Empty : Container
  | Full : StateRO -> Container.

Definition extract_from_container (c : Container) : nat :=
  match c with
  | Empty => 0
  | Full s => ro_value s + ro_data s
  end.

(* Variant: Nested match with reuse *)
Definition nested_reuse (t : Tree) : Tree :=
  let t2 := transform_tree t in
  transform_tree t2.

(* ===== FROM OwnedParam.v ===== *)

Record StateOP : Type := mkStateOP {
  op_value : nat;
  op_data : nat
}.

Definition identity (s : StateOP) : StateOP := s.

Definition extract_via_match (s : StateOP) : nat :=
  match identity s with
  | mkStateOP v d => v
  end.

Definition consume_state (s : StateOP) : StateOP := s.

Definition match_consumed (s : StateOP) : nat :=
  match consume_state s with
  | mkStateOP v d => v
  end.

Definition force_owned (s : StateOP) : StateOP * nat :=
  let result := match s with
                | mkStateOP v d => v
                end in
  (s, result).

Definition pair_then_match (s : StateOP) : (StateOP * StateOP) * nat :=
  let p := (s, s) in
  let x := match s with mkStateOP v d => v end in
  (p, x).

End ComprehensivePatterns.

Crane Extraction "comprehensive_patterns" ComprehensivePatterns.
