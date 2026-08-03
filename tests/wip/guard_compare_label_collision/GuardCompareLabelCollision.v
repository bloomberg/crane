From Crane Require Import Extraction.
From Stdlib Require Import Arith OrderedType.

(** Reproduces the documented `Crane Guard Compare` Label-keying bug (see
    docs/scan/117-guard-compare-directives-are-keyed-by-final-label-and-can-affect-unrelated-functions.md).

    `guard_compare_table` in src/table.ml is keyed by `Label.t`
    (`KerName.label`, i.e. just the trailing identifier, dropping the module
    path), not by full `GlobRef.t`. Two constants named [compare] in
    unrelated modules therefore collide in the table: registering a guard
    for one silently guards the other too, even though it is never named in
    any [Crane Guard Compare] directive.

    This matters because the guard's generated fast path is hardcoded to
    [return Datatypes::Comparison::EQ;], which only type-checks when the
    target's return type really is the plain extraction-primitive
    [comparison] type -- the shape ordinary [Fixpoint]-recursive comparators
    have (e.g. [OK.compare] below, or `re_compare` in a real grammar's
    lexer). [UsualOrderedType]-module-style comparators (used throughout
    FSet/FMap-backed structures, e.g. `SllSubparserAsUOT`/`CacheKeyAsUOT` in
    parse-a-lot's `SLLPrediction.v`) instead return the dependent
    [OrderedType.Compare lt eq x y] sig -- a different C++ type. [Ordered.t]
    below mimics that shape.

    Expected (buggy) result: extracting this file and compiling the
    generated C++ FAILS -- not because of anything wrong with [Ordered.compare]
    itself, but because the Label collision injects an ill-typed
    [Datatypes::Comparison::EQ] fast path into it, purely as a side effect of
    guarding the unrelated [OK.compare]. A fix that keys `guard_compare_table`
    by full [GlobRef.t] instead of [Label.t] should make this file extract
    and compile cleanly (with the guard applied only to [OK.compare]). *)

Module OK.
  (** An ordinary structural comparator returning the plain extraction
      primitive [comparison] -- the only shape `Crane Guard Compare`'s
      codegen actually supports. Guarding this one is fine: physical
      identity of the two arguments trivially implies structural equality
      for pure/immutable values. *)
  Fixpoint compare (x y : nat) : comparison :=
    match x, y with
    | O, O => Eq
    | O, S _ => Lt
    | S _, O => Gt
    | S x', S y' => compare x' y'
    end.
End OK.

Module Ordered.
  (** Unrelated type and module -- never mentioned in the [Crane Guard
      Compare] directive below. Its [compare] happens to share the trailing
      label "compare" with [OK.compare], which is all the Label-keyed table
      looks at. Mimics the real [UsualOrderedType]-module shape used by
      parse-a-lot's SLL prediction cache/set comparators. *)
  Inductive t := A | B.

  Definition eq (x y : t) : Prop := x = y.
  Definition lt (x y : t) : Prop := x = A /\ y = B.

  Lemma eq_refl : forall x, eq x x. Proof. reflexivity. Qed.
  Lemma eq_sym : forall x y, eq x y -> eq y x. Proof. unfold eq; congruence. Qed.
  Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
  Proof. unfold eq; congruence. Qed.
  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof. unfold lt; intros x y z [-> ->] [Heq _]; discriminate Heq. Qed.
  Lemma lt_not_eq : forall x y, lt x y -> ~ eq x y.
  Proof. unfold lt, eq; intros x y [-> ->]; discriminate. Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y.
    refine (match x, y with
            | A, A => EQ _
            | A, B => LT _
            | B, A => GT _
            | B, B => EQ _
            end); unfold lt, eq; auto.
  Defined.
End Ordered.

(* Intentionally guards only [OK.compare]. [Ordered.compare] is never named
   here -- but the Label-keyed table can't tell the two apart. *)
Crane Guard Compare OK.compare => Eq.

Crane Extraction "guard_compare_label_collision" OK Ordered.
