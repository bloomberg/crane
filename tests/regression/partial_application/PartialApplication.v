(** An instance of a higher-kinded one-method class, whose carrier has no C++
    name to deduce.

    A one-method class is a synonym, so [TFunctor] is emitted as

      template <template <typename> class t>
      using TFunctor = std::function<...>

    and its projection [tfmap] as a template over that [t], deduced at the call
    site from [t<T2> x0].  [TFunctor_pair]'s carrier is the anonymous
    [fun T => (T * box T)%type], and matching [t<T2>] against
    [std::pair<Nat, Box<Nat>>] deduces [t = std::pair], a binary template where
    a unary one was declared.  Deduction cannot succeed here, so the call
    spells the carrier: the front end recovers it by abstracting the expected
    result type over the instantiated element, and the printer mints the alias
    template [_crane_carrier_tc] for it.  Everything after the carrier still
    deduces, because an alias template is transparent.

    [box] is then read at another element type -- [Box<Nat>] reaching a slot
    spelled [Box<std::any>].  It is a flat single-constructor inductive, so it
    is emitted as an aggregate and cannot take the converting constructor the
    variant path uses; it carries a conversion function instead.  The
    composite carrier around it is read component-wise through the [std::pair]
    overload of [crane_cast_to], because [std::pair]'s own converting
    constructor asks each component to be constructible where an erased one
    needs a cast.

    Reduced from Vellvm's [Syntax/Traversal.v]. *)

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
