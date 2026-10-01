(** A let-bound lambda that lifts, inside a class-parameterised function, with
    the class instance free in its body.

    Vellvm install #10 (§190) turned eighteen of thirty-one errors into one
    family: five lifted helpers declared [const Params _tcI0] as a value
    parameter and called as [f<_tcI0>(a0, _tcI0)].  A concept is not a type, so
    the parameter is ill-formed; it also shadows the template parameter it is
    named after, and every use in the body then resolves to the value.

    [tests/regression/bind_continuation_binder_from_class_field] fixed exactly
    this on the lifted-{e fix} path and could not see it here, because its
    [fix] calls the enclosing [Fixpoint] and so stays inline.  The lifted-{e
    lambda} path is separate code and had the same defect.  This file is the
    lambda half, and it is the shape the Vellvm sites actually have: the
    lifted thing is a [let]-bound function, not a [fix].

    {b The differential, run before the fix existed and reproduced after it.}
    With the class-instance exclusion disabled and nothing else changed, this
    file emits

    {v
      auto _walk_step(const T1, const typename _tcI0::addr x,
                      const Params _tcI0) {
    v}

    --- the Vellvm signature exactly, with its three diagnostics: "expected
    'auto' or 'decltype(auto)' after concept name", "declaration of '_tcI0'
    shadows template parameter", and the unused parameter.  With the exclusion
    on, the parameter is absent and the instance travels only as the explicit
    template argument it already was.

    {b Why one filter now serves both paths.}  The exclusion, the [Tdummy] one
    and the void one are all answers to the same question --- which free rels
    of a lifted body are values there is anything to pass --- so they live in
    [Translation.lifted_free_vars] and both lift sites call it.  Having fixed
    the [fix] path alone once already, the duplicate was the defect. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Params := { addr : Type ; zero : addr ; bump : addr -> addr }.

Inductive box (P : Params) : Type :=
| Box : addr -> box P.

Arguments Box {P}.

(** [step] is [let]-bound, {e polymorphic} in its own [A] --- which is what
    sends it down the lift path rather than out as a [std::function] --- and
    the class instance is free in its body.  Vellvm's
    [_denote_exp_denote_exp_base] has exactly this shape: its own [typename
    T1] on top of the enclosing [Params _tcI0]. *)
Definition walk {P : Params} (n : nat) (a : addr) : box P :=
  let step := fun (A : Type) (_ : A) (x : addr) => Box (bump x) in
  match n with
  | O => step nat 0 a
  | S _ => step bool true (bump a)
  end.

#[global] Instance natParams : Params :=
  {| addr := nat ; zero := 0 ; bump := S |}.

Module LiftedLambdaPassesClassInstance.
  Definition run : box natParams := @walk natParams 1 0.
End LiftedLambdaPassesClassInstance.
Crane Extraction "lifted_lambda_passes_class_instance" LiftedLambdaPassesClassInstance.
