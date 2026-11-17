(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Crane Extraction Implicit f [ k ]] drops the [k]th parameter
    from [f]'s definition but not from its calls.  [count]'s recursive call
    and its caller still pass the dropped argument, and wrap the call in an
    eta lambda ([[=](List<..> _x0) { return count(a1_value, _x0); } + 1]):
    "too many arguments to function call, expected single argument 'l',
    have 2 arguments".  The same for a polymorphic [walk] with its implicit
    named. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module ExtractionImplicitCallSites.

Fixpoint count (unused : bool) (l : list nat) : nat :=
  match l with [] => 0 | _ :: t => S (count unused t) end.

Definition counted : nat := count false [1; 2; 3].

Fixpoint walk {A} (dflt : A) (l : list A) : nat :=
  match l with [] => 0 | _ :: t => S (walk dflt t) end.

Definition walked : nat := walk 0 [1; 2; 3] + walk true [false].

End ExtractionImplicitCallSites.

Crane Extraction Implicit ExtractionImplicitCallSites.count [ 1 ].
Crane Extraction Implicit ExtractionImplicitCallSites.walk [ dflt ].
Crane Extraction "extraction_implicit_call_sites" ExtractionImplicitCallSites.
