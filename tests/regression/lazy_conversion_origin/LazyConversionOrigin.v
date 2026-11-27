(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** A coinductive value converted to another instantiation of its type and
    back.  Converting back to the type the source was converted from is the
    source itself, so a value that goes out and back each round (an erased
    loop state) does not pile up a layer per round trip.  Only a conversion's
    lazy node remembers its source; a plain suspension's node does not carry
    those words.  The test checks both kinds of node, through the generated
    stream and through [crane::lazy] directly: run-once, a rethrown
    exception, the round trip, and the source being released with the
    conversion. *)
Require Import Crane.Mapping.NatInt.
Require Crane.Extraction.

Module LazyConversionOrigin.

CoInductive stream (A : Type) : Type :=
| SCons : A -> stream A -> stream A.

Arguments SCons {A} _ _.

CoFixpoint from (n : nat) : stream nat := SCons n (from (S n)).

CoFixpoint smap {A B : Type} (f : A -> B) (s : stream A) : stream B :=
  match s with
  | SCons x xs => SCons (f x) (smap f xs)
  end.

Definition hd {A : Type} (s : stream A) : A :=
  match s with
  | SCons x _ => x
  end.

Definition tl {A : Type} (s : stream A) : stream A :=
  match s with
  | SCons _ xs => xs
  end.

Fixpoint nth {A : Type} (n : nat) (s : stream A) : A :=
  match n with
  | O => hd s
  | S m => nth m (tl s)
  end.

Definition doubled (n : nat) : nat := nth n (smap (fun x => x + x) (from 0)).

End LazyConversionOrigin.

Crane Extraction "lazy_conversion_origin" LazyConversionOrigin.
