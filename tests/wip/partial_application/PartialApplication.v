(** Crane bug: an instance of a higher-kinded one-method class cannot be
    instantiated in C++.

    A one-method class is a synonym, so [TFunctor] is emitted as

      template <template <typename> class t>
      using TFunctor = std::function<...>

    and its projection [tfmap] as a template over that [t].  Neither the
    projection nor the instances can then be reached:

      - [tfmap]'s [t] is a template template parameter, and the call site
        deduces it from [t<T2> x0].  For [TFunctor_pair], whose carrier is the
        anonymous [fun T => (T * box T)%type], there is no C++ name to deduce
        to -- an alias template would not be deducible either, so the call
        would have to spell [t] explicitly.

      - The instance bodies erase their own type arguments, so [ft_box] and
        [ft_pair] are called with a [T2] that appears only in the return type
        and is left to deduction.

    Expected: extracted C++ compiles.
    Actual:   error: no matching function for call to 'ft_box'
              note: couldn't infer template argument 'T2'
              error: no matching function for call to 'tfmap'
              note: could not match 'TFunctor<T1>' against '(lambda ...)'

    The reduction originally recorded here -- "too few arguments to function
    call, expected 7, have 5", seen 22 times in Vellvm's
    [Syntax/Traversal.v] -- is fixed: an instance's declaration and its call
    sites now agree on how many arguments it takes, so the partial application
    [TFunctor_box Endo_id] is eta-expanded into a closure rather than emitted
    as a short call. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Class Endo (T : Set) := endo : T -> T.
Class TFunctor (T : Set -> Set) := tfmap : forall {U V : Set}, (U -> V) -> T U -> T V.

#[global] Instance Endo_id {T : Set} : Endo T := fun x => x.

Inductive box (T : Set) : Set := mk (tag : nat) (t : T).
Arguments mk {T}.

Definition ft_box {U V : Set} (f : U -> V) (b : box U) : box V :=
  match b with mk n t => mk (endo n) (f t) end.

#[global] Instance TFunctor_box `{Endo nat} : TFunctor box :=
  fun U V f => ft_box f.

Definition ft_pair {U V : Set} `{TFunctor box} (f : U -> V) (p : U * box U) : V * box V :=
  match p with (u, b) => (f u, tfmap f b) end.

#[global] Instance TFunctor_pair `{TFunctor box} : TFunctor (fun T => (T * box T)%type) :=
  fun U V f => ft_pair f.

Module PartialApplication.

  Definition convert (p : nat * box nat) : bool * box bool :=
    tfmap (TFunctor := TFunctor_pair (H := TFunctor_box (H := Endo_id)))
          (fun n : nat => Nat.eqb n 0) p.

End PartialApplication.

Crane Extraction "partial_application" PartialApplication.
