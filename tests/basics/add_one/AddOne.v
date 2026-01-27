(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Testing calling C++ functions from Rocq *)
(* https://rocq-prover.org/doc/V9.0.0/refman/addendum/extraction.html#realizing-axioms *)

Axiom zero : nat.
Axiom add_one : nat -> nat.

Definition one : nat := add_one zero.

Require Crane.Extraction.
Crane Extract Inlined Constant zero => "Nat::nat::ctor::O_()" From "functional".
Crane Extract Inlined Constant add_one => "Nat::nat::ctor::S_(%a0)".
Crane Extraction "add_one" one.
