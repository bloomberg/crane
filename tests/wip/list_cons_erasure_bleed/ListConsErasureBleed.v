From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.DequeList.
From Stdlib Require Import List.
Import ListNotations.

(** Compile-time repro. After Defs.v's [rev_tuple_cons_case] singleton-tuple
    erasure bug was fixed (previous wip: erased_singleton_unit_tuple), the
    generated code for [rev_tuple_cons_case] now correctly emits a properly
    erased [pair<any,any>] for the value tuple -- but a NEW bug appeared in
    the SAME function: it also builds the CONCRETE singleton grammar-symbol
    list [x] (a plain [list symbol], NOT an erased [symbols_semty] value),
    and this now ALSO gets erased/mis-typed, e.g. (observed in
    benchmarking/crane_extracted/Benchmarking/Defs.h):

      [](auto _a0, auto _a1) { _a1.push_front(_a0); return _a1; }(
          std::any(std::move(x)), std::deque<Symbol>{})

    where [_a1] is [std::deque<Symbol>], so [push_front] requires a concrete
    [Symbol], not [std::any] -- "no matching member function for call to
    'push_front'".

    This file mirrors [theories/Parser/Defs.v]'s [concat_tuple]/[rev_tuple]
    family verbatim (same tactic-built dependent-case-split style, same
    [symbols_semty gamma := tuple (map symbol_semty gamma)] domain), with
    [sym] standing in for [symbol]. [rev_tuple_cons_case] calls
    [concat_tuple (rev xs') [x] (f xs' vs) (v, tt)] -- exactly like the real
    one -- where [[x] : list sym] is a concrete singleton grammar-symbol list
    built in the SAME function that also builds the erased singleton value
    tuple [(v, tt) : syms_semty [x]]. [check] forces [rev_tuple] on a
    two-element list so Crane must extract [rev_tuple_cons_case] for real. *)

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

Inductive sym := A | B.
Definition sym_semty (s : sym) : Type := nat.
Definition syms_semty (g : list sym) : Type := tuple (map sym_semty g).

Definition concat_tuple_nil_case :
  forall (xs ys : list sym)
         (vs    : syms_semty xs)
         (vs'   : syms_semty ys)
         (heq   : xs = []),
    syms_semty (xs ++ ys).
  intros xs ys vs vs' heq; subst; auto.
Defined.

Definition concat_tuple_rec_case :
  forall (x         : sym)
         (xs' xs ys : list sym)
         (vs        : syms_semty xs)
         (vs'       : syms_semty ys)
         (f         : forall xs ys, syms_semty xs -> syms_semty ys -> syms_semty (xs ++ ys))
         (heq       : xs = x :: xs'),
    syms_semty (xs ++ ys).
  intros x xs' xs ys vs vs' f heq; subst; simpl in vs.
  destruct vs as (v, vs).
  simpl; constructor.
  - exact v.
  - apply f; auto.
Defined.

Fixpoint concat_tuple
           (xs ys : list sym)
           (vs    : syms_semty xs)
           (vs'   : syms_semty ys) : syms_semty (xs ++ ys) :=
  match xs as xs' return xs = xs' -> _ with
  | []       => fun heq => concat_tuple_nil_case xs ys vs vs' heq
  | x :: xs' => fun heq => concat_tuple_rec_case x xs' xs ys vs vs' concat_tuple heq
  end eq_refl.

Definition rev_tuple_nil_case :
  forall (xs : list sym) (vs : syms_semty xs) (heq : xs = []),
    syms_semty (rev xs).
  intros; subst; auto.
Defined.

Definition rev_tuple_cons_case :
  forall (xs  : list sym)
         (x   : sym)
         (xs' : list sym)
         (heq : xs = x :: xs')
         (vs  : syms_semty xs)
         (f   : forall xs, syms_semty xs -> syms_semty (rev xs)),
    syms_semty (rev xs).
  intros xs x xs' heq vs f; subst; simpl in vs.
  destruct vs as (v, vs).
  exact (concat_tuple (rev xs') [x] (f xs' vs) (v, tt)).
Defined.

Fixpoint rev_tuple (xs : list sym) (vs : syms_semty xs) : syms_semty (rev xs) :=
  match xs as xs' return xs = xs' -> _ with
  | []       => fun heq => rev_tuple_nil_case xs vs heq
  | x :: xs' => fun heq => rev_tuple_cons_case xs x xs' heq vs rev_tuple
  end eq_refl.

Definition check (n : nat) : nat :=
  match rev_tuple [A; B] (n, (n, tt)) with (v, _) => v end.

Crane Extraction "list_cons_erasure_bleed" check.
