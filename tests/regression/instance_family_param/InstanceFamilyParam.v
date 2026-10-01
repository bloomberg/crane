(** Crane bug: a type-class instance parametric over an event family
    ([Instance Functor_box {E : Type -> Type} : Functor (box E)]) is emitted
    as a non-template struct, and the family leaks as a bare placeholder [_].

    Observed:
      struct Functor_box {
        template <typename _A0> using F = box<_<std::any>, _A0>;
        template <typename _A0, typename _A1>
        static box<_<_A1>, _A1> fmap(std::function<_A1(_A0)> f, ...
      static_assert(Functor<Functor_box>);
    Diagnostics:
      error: use of undeclared identifier '_'
      error: static assertion failed
    Expected: something like [template <typename E> struct Functor_box] with
    [F = box<E, _A0>], instantiated at the use ([box noE nat]).

    This is ITree's [Functor (itree E)] / [Monad (itree E)] /
    [MonadIter (itree E)] instances (ExtLib classes), which [interp],
    [ITree.map] and every [x <- t ;; k] under the Monad notation go through.
    Reduced from Vellvm's vanilla-ITree extraction (the [Functor_itree] /
    [Monad_itree] structs, e.g. [template <typename _A0> using F =
    Itree<_<std::any>, _A0>;]) and from a small ITree [interp] probe. *)

From Crane Require Import Extraction.
From Crane Require Import Mapping.Std.

Module InstanceFamilyParam.
  Class Functor (F : Type -> Type) : Type :=
    { fmap : forall {A B : Type}, (A -> B) -> F A -> F B }.

  Inductive box (E : Type -> Type) (A : Type) : Type := Box (a : A).
  Arguments Box {E A}.

  (* ITree's [Functor (itree E)] / [Monad (itree E)] shape: an instance
     parametric over a family. *)
  #[global] Instance Functor_box {E : Type -> Type} : Functor (box E) :=
    { fmap := fun A B f b => match b with Box a => Box (f a) end }.

  Variant noE : Type -> Type := .

  Definition b : box noE nat := fmap S (Box 2).
  Definition is_three : bool := match b with Box n => Nat.eqb n 3 end.
End InstanceFamilyParam.

Crane Extraction "instance_family_param" InstanceFamilyParam.
