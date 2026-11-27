(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Testing calling C++ functions from Rocq *)
(* https://rocq-prover.org/doc/V9.0.0/refman/addendum/extraction.html#realizing-axioms *)

Axiom zero : nat.
Axiom add_one : nat -> nat.

Definition one : nat := add_one zero.

From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
Require Crane.Extraction.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.
#[global] Instance zero_mapping : OperationMapping (Ref (@zero)) :=
  pure_cpp ["functional"] []
    (Structured (Verbatim "Nat::o()")).
#[global] Instance add_one_mapping : OperationMapping (Ref (@add_one)) :=
  pure_cpp [] ["x0"]
    (Structured (Call "Nat::s" [] [Arg "x0"])).
Crane Extraction "add_one" one.
