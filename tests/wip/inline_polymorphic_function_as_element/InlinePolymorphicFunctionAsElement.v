(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: [Crane Extraction Inline] of a polymorphic higher-order
    function, used partially applied as a list element ([[twice S]]), does
    not compile.  The inlined body's [let f := S] is lifted to
    [template <typename T1> T1 fs_crane_f(uint64_t)], whose result type no
    call can deduce, and called at [crane::obj]: "no matching function for
    call to 'fs_crane_f'".  The same code written out by hand compiles, and
    inlining [twice] where it is called works. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module InlinePolymorphicFunctionAsElement.

Definition twice {A} (f : A -> A) (x : A) := f (f x).

Definition fs : list (nat -> nat) := [twice S].

Definition result : nat := fold_left (fun a f => f a) fs 1.

End InlinePolymorphicFunctionAsElement.

Crane Extraction Inline InlinePolymorphicFunctionAsElement.twice.
Crane Extraction "inline_polymorphic_function_as_element" InlinePolymorphicFunctionAsElement.
