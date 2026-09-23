(* A callable parameter whose argument list only exists after erasure is
   spelled [std::function<bool(T1)>] rather than generalised to an [F &&], and
   that spelling is a deduced context.  A lambda never has a [std::function]
   type, so deduction does not merely decline to contribute -- it fails, and
   the candidate is discarded before the conversion that would have succeeded
   is considered:

     error: no matching function for call to 'forall_dec'
     note: candidate template ignored: could not match
           'std::function<bool (T1)>' against '(lambda at ...)'

   The erased argument is what selects the spelled form.  [In a l] is a proof,
   so the extracted parameter is [A -> bool] -- an arrow that exists only after
   erasure rather than one written in the source.  Dropping the proof argument
   gives the generic deducible form and no error.

   The spelled form is nevertheless the right one.  [forall_dec] rebuilds its
   callable at each recursive step, because the hypothesis mentions [l] and has
   to be re-abstracted for the tail; under an [F &&] every step would be a new
   closure type and so a new specialisation, and the instantiation never
   closes.  The [std::function] is a type-erasure boundary doing real work.  So
   the defect is narrow: the required form was left somewhere it gets deduced
   against.

   The control is inside the generated code -- [forall_dec]'s own recursive
   call passes a lambda to this same parameter and compiles, because it names
   [T1] explicitly and no deduction runs.

   Reduced from Vellvm's ListUtil.FORALL_dec (rocq/Utils/ListUtil.v:518),
   reached from DynamicTypes.NO_VOID_dec. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.
From Stdlib Require Import List PeanoNat Bool.
Import ListNotations.

Fixpoint FORALL {A} (P : A -> Prop) (l : list A) : Prop :=
  match l with [] => True | x :: xs => P x /\ FORALL P xs end.

(** [In a l] is a proof argument and erases away, so the extracted parameter is
    a bare [A -> bool]. *)
Lemma forall_dec : forall {A} (P : A -> Prop) (l : list A)
    (H : forall a, In a l -> {P a} + {~ P a}),
    {FORALL P l} + {~ FORALL P l}.
Proof.
  intros A P l. induction l; intros HD.
  - left. exact I.
  - destruct (HD a (or_introl eq_refl)) as [Hp | Hp].
    + destruct (IHl (fun x Hx => HD x (or_intror Hx))) as [Hr | Hr].
      * left. split; assumption.
      * right. intros [_ C]. exact (Hr C).
    + right. intros [C _]. exact (Hp C).
Defined.

Definition small (n : nat) : Prop := Nat.ltb n 10 = true.

Definition small_dec (n : nat) : {small n} + {~ small n} :=
  Bool.bool_dec (Nat.ltb n 10) true.

(** The call site that fails: a lambda passed where deduction runs. *)
Definition allsmall (l : list nat) : bool :=
  if forall_dec small l (fun a _ => small_dec a) then true else false.

Crane Extraction "erased_arg_callable_spelled_std_function" allsmall.
