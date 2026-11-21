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
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

(** [nat] is an [unsigned int]: [O] is [0], [S n] is [n + 1], a match
    tests [n <= 0] and reads the predecessor as [n - 1], and a numeral is
    a [u]-suffixed literal. *)
#[export] Instance bde_nat_mapping : TypeMapping nat :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "unsigned int";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews nat;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref O;
             ctor_build := Expr "0";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut <= 0";
                       case_fields := [] |} |};
          {| ctor_source := Ref S;
             ctor_build := Expr "(%a0 + 1)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut > 0";
                       case_fields := [(0, OwnedProjection "%scrut - 1")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref O; numeral_action := NumeralZero |};
                  {| numeral_constructor := Ref S; numeral_action := NumeralSuccessor 0 |}];
               numeral_emitter := IntegerToken "" "u";
               numeral_converters := [Ref Nat.of_num_uint] |} |}.

#[export] Instance bde_nat_add_mapping : OperationMapping (Ref Nat.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_mul_mapping : OperationMapping (Ref Nat.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) * %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_div_mapping : OperationMapping (Ref Nat.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) ? %arg(x) / %arg(y) : 0)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_modulo_mapping : OperationMapping (Ref Nat.modulo) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) ? %arg(x) % %arg(y) : %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_double_mapping : OperationMapping (Ref Nat.double) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) + %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_pred_mapping : OperationMapping (Ref Nat.pred) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) ? %arg(n) - 1 : %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_sub_mapping : OperationMapping (Ref Nat.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(((%arg(n) - %arg(m)) > %arg(n) ? 0 : (%arg(n) - %arg(m))))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_max_mapping : OperationMapping (Ref Nat.max) :=
  {| operation_headers := ["bsl_algorithm.h"];
     operation_cpp := Expr "bsl::max(%arg(n), %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_min_mapping : OperationMapping (Ref Nat.min) :=
  {| operation_headers := ["bsl_algorithm.h"];
     operation_cpp := Expr "bsl::min(%arg(n), %arg(m))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_eqb_mapping : OperationMapping (Ref Nat.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_ltb_mapping : OperationMapping (Ref Nat.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) < %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_leb_mapping : OperationMapping (Ref Nat.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) <= %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_nat_compare_mapping : OperationMapping (Ref Nat.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(n) < %arg(m) ? %ret::LT : (%arg(m) < %arg(n) ? %ret::GT : %ret::EQ))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance bde_nat_iter_mapping : OperationMapping (Ref Nat.iter) :=
  {| operation_headers := ["type_traits"; "utility"];
     operation_cpp := Expr "[](unsigned int _crane_n, auto _crane_f, auto _crane_seed) { %ret _crane_acc = std::move(_crane_seed); for (unsigned int _crane_i = 0; _crane_i < _crane_n; _crane_i++) { _crane_acc = _crane_f(std::move(_crane_acc)); } return _crane_acc; }(%arg(n), %arg(f), %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "f"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* [PeanoNat.Nat] includes [Nat]: its [add], [mul], ... are the same
   constants, mapped above; only [eq_dec] is its own. *)
From Stdlib Require PeanoNat.

#[export] Instance bde_peano_nat_eq_dec_mapping : OperationMapping (Ref PeanoNat.Nat.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(n) == %arg(m)";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.


From Corelib Require Import PrimInt63.
Axiom nat_of_int : int -> nat.
#[export] Instance bde_nat_of_int_mapping : OperationMapping (Ref nat_of_int) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<unsigned int>(%arg(x0))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x0"; argument_use := Read |}]
         ReturnValue [] |}.



From Corelib Require Import PrimString.
Axiom string_of_nat : nat -> string.
#[export] Instance bde_string_of_nat_mapping : OperationMapping (Ref string_of_nat) :=
  {| operation_headers := ["bsl_string.h"];
     operation_cpp := Expr "bsl::to_string(%arg(x0))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x0"; argument_use := Read |}]
         ReturnValue [] |}.
