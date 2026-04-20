From Crane Require Import Extraction.
From Crane.Mapping Require Import Std.
Require Import Crane.Mapping.NatIntStd.

Module LetPairShadow.

(** BUG: Two sequential [let '(a, b) := f x] destructurings of COMPUTED
    pair results in the same scope both generate the C++ temporary name
    [_cs]. The second declaration shadows the first, producing invalid
    C++ (redefinition error).

    Root cause: the pair-destructuring temporary [_cs] is not uniquified
    per destructuring site. Each [let '(x, y) := expr] where [expr] is
    a function call emits:
      auto _cs = expr;
      const T& x = _cs.first;
      const T& y = _cs.second;
    When two such destructurings appear in sequence, the second
    [auto _cs = ...] collides with the first.

    Note: simple variable RHS ([let '(x,y) := p]) does NOT create a
    temporary — it accesses [p.first]/[p.second] directly. The bug
    only fires when the RHS is a computed expression (function call,
    constructor application, etc.).

    This is a codegen/compilation-failure bug. *)

Inductive mylist (A : Type) : Type :=
| mynil : mylist A
| mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A}.

Fixpoint mylist_sum (l : mylist nat) : nat :=
  match l with
  | mynil => 0
  | mycons h t => h + mylist_sum t
  end.

(** Pattern 1: [map_accum] — two sequential pair destructurings of
    function-call results in the same match branch. *)
Fixpoint map_accum {A B S : Type} (f : S -> A -> S * B) (acc : S)
    (l : mylist A) : mylist B * S :=
  match l with
  | mynil => (mynil, acc)
  | mycons x xs =>
    let '(new_acc, y) := f acc x in
    let '(rest, final_acc) := map_accum f new_acc xs in
    (mycons y rest, final_acc)
  end.

(** test1: map_accum with running sum.
    f(acc, x) = (acc+x, acc).
    map_accum f 0 [10,20,30] = ([0,10,30], 60)
    sum(list) + acc = 40 + 60 = 100 *)
Definition test1 : nat :=
  let '(l, acc) := map_accum (fun s x => (s + x, s)) 0
    (mycons 10 (mycons 20 (mycons 30 mynil))) in
  mylist_sum l + acc.

(** Helper functions that return pairs (force temporary allocation). *)
Definition add_pair (a b : nat) : nat * nat := (a + b, a * b).
Definition sub_pair (a b : nat) : nat * nat := (a - b, a + b).

(** Pattern 2: Two destructs of function-call results in top-level body. *)
Definition double_call_destruct (a b c d : nat) : nat :=
  let '(sum_ab, prod_ab) := add_pair a b in
  let '(diff_cd, sum_cd) := sub_pair c d in
  sum_ab + prod_ab + diff_cd + sum_cd.

(** test2: add_pair 3 4 = (7, 12), sub_pair 10 3 = (7, 13)
    7 + 12 + 7 + 13 = 39 *)
Definition test2 : nat := double_call_destruct 3 4 10 3.

(** Pattern 3: Three destructs of function-call results. *)
Definition triple_call_destruct (a b c d e f : nat) : nat :=
  let '(r1, r2) := add_pair a b in
  let '(r3, r4) := add_pair c d in
  let '(r5, r6) := add_pair e f in
  r1 + r2 + r3 + r4 + r5 + r6.

(** test3: add_pair 1 2 = (3,2), add_pair 3 4 = (7,12),
    add_pair 5 6 = (11,30).  3+2+7+12+11+30 = 65 *)
Definition test3 : nat := triple_call_destruct 1 2 3 4 5 6.

End LetPairShadow.

Crane Extraction "let_pair_shadow" LetPairShadow.
