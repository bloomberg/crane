(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Crane bug: an explicit template argument standing for a function type of
    two or more arguments is printed curried, while values of that type are
    flat.  A [nat -> nat -> nat] is a [crane::fn<uint64_t(uint64_t,
    uint64_t)>] as a field, a list element or a declaration, but a call's
    type argument goes through a conversion that curries it:
    - [wrap Nat.add] calls [wrap<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>>]
      to initialise a [List<crane::fn<uint64_t(uint64_t, uint64_t)>>];
    - [List.map A [1;2]], [A] a three-field constructor, instantiates
      [map] at the curried type with a flat-returning lambda;
    - [myfst pf] instantiates [myfst] curried where [pf]'s component is
      flat. *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Crane Require Import Extraction.
From Crane Require Import Mapping.NatIntStd.

Module FunctionTypeArgumentCurried.

Definition idp {A} (x : A) : A := x.
Definition f2 : nat -> nat -> nat := idp Nat.add.

Definition wrap {A} (x : A) : list A := [x].
Definition ws : list (nat -> nat -> nat) := wrap Nat.add.
Definition from_wrap : nat := match ws with g :: _ => g 3 4 | [] => 0 end.

Inductive t := A : nat -> nat -> nat -> t.
Definition ev (x : t) : nat := match x with A a b c => a + b + c end.
Definition fs : list (nat -> nat -> t) := List.map A [1; 2].
Definition from_ctor : nat := fold_left (fun acc f => acc + ev (f 0 5)) fs 0.

Definition myfst {X Y} (p : X * Y) : X := match p with (a, _) => a end.
Definition pf : (nat -> nat -> nat) * nat := (Nat.add, 1).
Definition from_pair : nat := (myfst pf) 2 3.

Definition result : nat := f2 1 2 + from_wrap + from_ctor + from_pair.

End FunctionTypeArgumentCurried.

Crane Extraction "function_type_argument_curried" FunctionTypeArgumentCurried.
