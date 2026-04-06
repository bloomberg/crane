(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Std.

(** Extraction of [nat] to GMP's [mpz_class] (arbitrary-precision integers).

    This maps Peano-style [nat] to the C++ wrapper [mpz_class] from
    [<gmpxx.h>], providing unlimited precision arithmetic.

    Requirements:
    - GMP library installed with C++ bindings (libgmpxx)
    - Link with [-lgmpxx -lgmp]
*)

Crane Extract Inductive nat =>
  "mpz_class"
  [ "mpz_class(0)" "(mpz_class(%a0) + 1)" ]
  "if (%scrut <= 0) { %br0 } else { mpz_class %b1a0 = %scrut - 1; %br1 }"
  From "gmpxx.h".

Crane Extract Numeral nat => "mpz_class(%n)".

Crane Extract Inlined Constant Nat.add => "(%a0 + %a1)".
Crane Extract Inlined Constant Nat.mul => "(%a0 * %a1)".
Crane Extract Inlined Constant Nat.div => "(%a1 ? %a0 / %a1 : mpz_class(0))".
Crane Extract Inlined Constant Nat.modulo => "(%a1 ? %a0 % %a1 : %a0)".
Crane Extract Inlined Constant Nat.double => "(%a0 + %a0)".
Crane Extract Inlined Constant Nat.pred => "(%a0 > 0 ? %a0 - 1 : %a0)".
Crane Extract Inlined Constant Nat.sub => "(%a0 >= %a1 ? %a0 - %a1 : mpz_class(0))".
Crane Extract Inlined Constant Nat.max => "(%a0 >= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant Nat.min => "(%a0 <= %a1 ? %a0 : %a1)".
Crane Extract Inlined Constant Nat.eqb => "%a0 == %a1".
Crane Extract Inlined Constant Nat.ltb => "%a0 < %a1".
Crane Extract Inlined Constant Nat.leb => "%a0 <= %a1".

From Corelib Require Import PrimInt63.
Axiom nat_of_int : int -> nat.
Crane Extract Inlined Constant nat_of_int => "mpz_class(%a0)".

From Corelib Require Import PrimString.
Axiom string_of_nat : nat -> string.
Crane Extract Inlined Constant string_of_nat => "%a0.get_str()".
