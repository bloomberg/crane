(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Test: Mutually inductive types inside a module *)

From Stdlib Require Import NArith.
Open Scope nat_scope.

(* A simple module containing mutually inductive types *)
Module EvenOdd.
  (* Mutually inductive definition of even and odd lists *)
  Inductive even_list : Type :=
  | ENil : even_list
  | ECons : nat -> odd_list -> even_list
  with odd_list : Type :=
  | OCons : nat -> even_list -> odd_list.

  (* Functions operating on the mutual inductives *)
  Fixpoint even_length (e : even_list) : nat :=
    match e with
    | ENil => 0
    | ECons _ o => S (odd_length o)
    end
  with odd_length (o : odd_list) : nat :=
    match o with
    | OCons _ e => S (even_length e)
    end.

  (* Example values *)
  Definition empty : even_list := ENil.
  Definition one : odd_list := OCons 1 ENil.
  Definition two : even_list := ECons 2 (OCons 1 ENil).
  Definition three : odd_list := OCons 3 (ECons 2 (OCons 1 ENil)).
End EvenOdd.

(* Test values *)
Definition test_even_len := EvenOdd.even_length EvenOdd.two.
Definition test_odd_len := EvenOdd.odd_length EvenOdd.three.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Require Crane.Mapping.NatIntStd.

Crane Extraction "mutual_mod" test_even_len test_odd_len.

(* OCaml extraction for differential testing *)
From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Extraction "mutual_mod_ocaml.ml" test_even_len test_odd_len.
