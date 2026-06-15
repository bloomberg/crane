From Crane Require Import Mapping.NatIntStd.
From Crane Require Extraction.

(** Shape 1: a [let]-bound compound expression computed after the recursive
    call.  The generated continuation frame is pushed with a variable
    ([here]) that is only declared and computed later, inside the
    continuation branch: C++ compile error. *)
Fixpoint sum_signum (n : nat) : nat :=
  match n with
  | O => O
  | S n' =>
      let rest := sum_signum n' in
      let here := if Nat.eqb n' 0 then 0 else 1 in
      rest + here
  end.

(** Shape 2: a recursive call under a conditional inside a [let].  The
    generated continuation branch assigns to a variable ([rest]) declared in
    a different scope, and the consumer of [rest] runs before the recursive
    frame is processed: C++ compile error, and wrong scheduling besides.

    [down_let n] computes [n-1; n-2; ...; 0]: for example,
    [down_let 3 = [2; 1; 0]]. *)
Fixpoint down_let (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' =>
      let rest := if Nat.eqb n' 0 then nil else down_let n' in
      cons n' rest
  end.

(** Shape 3: the same function as shape 2 with the [let] inlined, so the
    recursive call sits under a conditional inside a constructor argument.
    This one compiles, but the generated loop drops the [cons] entirely:
    [down_inline 3] equals [[2; 1; 0]] in Rocq, yet extracts to code that
    returns [].  Plain [cons n' (down_inline n')] with the recursive call
    directly in argument position is handled correctly. *)
Fixpoint down_inline (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => cons n' (if Nat.eqb n' 0 then nil else down_inline n')
  end.

Example down_inline_semantics : down_inline 3 = cons 2 (cons 1 (cons 0 nil)).
Proof. reflexivity. Qed.

Set Crane Loopify.
Crane Extraction "loopify_nested_calls" sum_signum down_let down_inline.
