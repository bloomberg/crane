(** The typed-fit check under [CRANE_CHECK_IR] lets a pair of a known
    defect class through by its structure ([Typed_checks.known_class]),
    whatever declaration it is in: the test suite's allowlist names its
    declarations, and a program of its own meets the same classes under
    names of its own.  Found by Ephyra round 24, which hit allowlisted
    classes under new declarations and failed extraction.

    - [event]: [trigger Ask] passes the family [askE] where the slot reads
      it applied to its index;
    - [carrier]: a class over a type constructor, [Measured F], whose
      method is called at [list]: the argument [list nat] is put in a slot
      spelled as the instance's carrier applied, [app(ML)<nat>].

    Expected: extracts under [CRANE_CHECK_IR]; [answered = true],
    [measure_three = 3]. *)
From Crane Require Import Extraction.
From Crane Require Import Mapping.Std Mapping.NatInt.
From ITree Require Import ITree.
Import ITreeNotations.
Local Open Scope itree_scope.

Module TypedFitKnownClass.
  Variant askE : Type -> Type := Ask : askE nat.

  Definition program : itree askE nat :=
    x <- trigger Ask ;; y <- trigger Ask ;; Ret (x + y).

  Fixpoint answer (fuel : nat) (t : itree askE nat) : option nat :=
    match fuel with
    | O => None
    | S f =>
      match observe t with
      | RetF r => Some r
      | TauF t' => answer f t'
      | VisF e k =>
        match e in askE T return (T -> itree askE nat) -> option nat with
        | Ask => fun k => answer f (k 3)
        end k
      end
    end.

  Definition answered : bool :=
    match answer 100 program with Some n => Nat.eqb n 6 | None => false end.

  Class Measured (F : Type -> Type) := { measure : forall A : Type, F A -> nat }.
  Arguments measure {F _ A} _.

  Fixpoint count {A} (l : list A) : nat :=
    match l with nil => 0 | cons _ r => S (count r) end.

  #[global] Instance ML : Measured list := { measure := fun A l => count l }.

  Definition measure_list (l : list nat) : nat := measure l.
  Definition measure_three : nat := measure_list (cons 1 (cons 2 (cons 3 nil))).
End TypedFitKnownClass.

Crane Extraction "typed_fit_known_class" TypedFitKnownClass.
