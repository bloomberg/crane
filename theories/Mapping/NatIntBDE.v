(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [nat] (Peano naturals) to [unsigned int] (BDE flavor).

    Disclaimer: trying to obtain efficient certified programs
    by extracting [nat] into [int] is definitively *not* a good idea:

    - This is just a syntactic adaptation, many things can go wrong,
    such as name captures.

    - Since [int] is bounded while [nat] is (theoretically) infinite,
    you have to make sure by yourself that your program will not
    manipulate numbers greater than [max_int]. Otherwise you should
    consider the translation of [nat] into [big_int].

    - Moreover, the mere translation of [nat] into [int] does not
    change the complexity of functions. For instance, [mult] stays
    quadratic. To mitigate this, we propose here a few efficient (but
    uncertified) realizers for some common functions over [nat].

    This file is hence provided mainly for testing / prototyping
    purpose. For serious use of numbers in extracted programs,
    you are advised to use either Rocq advanced representations
    (positive, Z, N, BigN, BigZ) or modular/axiomatic representation.
*)
From Crane Require Extraction.
From Crane Require Export Mapping.BDE.

Crane Extract Inductive nat =>
  "unsigned int"
  [ "0" "(%a0 + 1)" ]
  "if (%scrut <= 0) { %br0 } else { unsigned int %b1a0 = %scrut - 1; %br1 }".

Crane Extract Numeral nat => "%nu".

Crane Extract Inlined Constant Nat.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Nat.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant Nat.modulo => "(%a0 % %a1)".
Crane Extract Inlined Constant Nat.double => "(%a0 + %a0)".
Crane Extract Inlined Constant Nat.pred => "(%a0 ? %a0 - 1 : %a0)".
Crane Extract Inlined Constant Nat.sub => "(((%a0 - %a1) > %a0 ? 0 : (%a0 - %a1)))".
Crane Extract Inlined Constant Nat.max => "bsl::max(%a0, %a1)" From "bsl_algorithm.h".
Crane Extract Inlined Constant Nat.min => "bsl::min(%a0, %a1)" From "bsl_algorithm.h".
Crane Extract Inlined Constant Nat.eqb => "%a0 == %a1".
Crane Extract Inlined Constant Nat.ltb => "%a0 < %a1".
Crane Extract Inlined Constant Nat.leb => "%a0 <= %a1".


Crane Extract Inlined Constant Nat.iter =>
  "[&]() { auto _acc = %a2; for (unsigned int _i = 0; _i < %a0; _i++) { _acc = %a1(std::move(_acc)); } return _acc; }()".

From Corelib Require Import PrimInt63.
Axiom nat_of_int : int -> nat.
Crane Extract Inlined Constant nat_of_int => "static_cast<unsigned int>(%a0)".

From Corelib Require Import PrimString.
Axiom string_of_nat : nat -> string.
Crane Extract Inlined Constant string_of_nat => "bsl::to_string(%a0)" From "bsl_string.h".
