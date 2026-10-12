(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: a polymorphic function bound by [let] and used at two different
    instances is declared at its result type.  [wrap] in [both] is applied at
    [A] and at [nat]; the binding is kept local, but declared
    [List<crane::obj> wrap = [](crane::obj x) { ... }] -- the type of what it
    returns, not of the function: "no viable conversion from '(lambda ...)'
    to 'List<crane::obj>'", and then "type 'List<crane::obj>' does not
    provide a call operator".  A binding used at one instance is fine
    ([regression/lifted_let_lambda_polymorphic]). *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module LetFunctionTwoInstances.

Definition both {A : Type} (a : A) : list A * list nat :=
  let wrap := fun (B : Type) (x : B) => [x] in
  (wrap A a, wrap nat 4).

Definition result : nat := List.length (fst (both 7)) + List.length (snd (both 7)).

End LetFunctionTwoInstances.

Crane Extraction "let_function_two_instances" LetFunctionTwoInstances.
