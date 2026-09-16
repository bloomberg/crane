(** Crane bug: a typeclass instance built by *application* of another instance
    is emitted as a call with too few arguments.

    [TFunctor_pair] takes a [TFunctor box] instance.  Crane cannot pass it as a
    template type argument (only constant instances get that treatment), so it
    falls back to building the instance as a value, and emits

      TFunctor_pair([]() { return TFunctor_box(Endo_id<Nat>); }())

    where [TFunctor_box] is the 3-argument [ft_box] under a different name.

    Expected: extracted C++ compiles.
    Actual:   error: no matching function for call to 'ft_box'
              note: candidate function template not viable: requires 3
                    arguments, but 1 was provided
              error: couldn't infer template argument 'T2'

    Seen in Vellvm as "too few arguments to function call, expected 7, have 5"
    (22 times), from the instances in [Syntax/Traversal.v]. *)

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
