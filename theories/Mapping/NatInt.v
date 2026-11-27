(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [nat] (Peano naturals) to [uint64_t] (std flavor).

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
From Crane Require Export Mapping.Std.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.
Import Crane.Cpp.

(** [nat] is a [uint64_t]: [O] is [0], [S n] is [n + 1], a match tests
    [n <= 0] and reads the predecessor as [n - 1], and a numeral is a
    [UINT64_C] literal. *)
#[export] Instance std_nat_mapping : TypeMapping nat :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Int Crane.Cpp.U64;
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
               numeral_emitter := IntegerToken "UINT64_C(" ")";
               numeral_converters := [Ref Nat.of_num_uint] |} |}.

#[export] Instance std_nat_add_mapping : OperationMapping (Ref Nat.add) :=
  pure [] ["n"; "m"] (Binop (Add Unchecked) (Arg "n") (Arg "m")).
#[export] Instance std_nat_mul_mapping : OperationMapping (Ref Nat.mul) :=
  pure [] ["n"; "m"] (Binop (Mul Unchecked) (Arg "n") (Arg "m")).
#[export] Instance std_nat_div_mapping : OperationMapping (Ref Nat.div) :=
  pure [] ["x"; "y"] (Cond (Arg "y") (Binop Div (Arg "x") (Arg "y")) (lit 0)).
#[export] Instance std_nat_modulo_mapping : OperationMapping (Ref Nat.modulo) :=
  pure [] ["x"; "y"] (Cond (Arg "y") (Binop Mod (Arg "x") (Arg "y")) (Arg "x")).
#[export] Instance std_nat_double_mapping : OperationMapping (Ref Nat.double) :=
  pure [] ["n"] (Binop (Add Unchecked) (Arg "n") (Arg "n")).
#[export] Instance std_nat_pred_mapping : OperationMapping (Ref Nat.pred) :=
  pure [] ["n"] (Cond (Arg "n") (Binop (Sub Unchecked) (Arg "n") (lit 1)) (Arg "n")).
#[export] Instance std_nat_sub_mapping : OperationMapping (Ref Nat.sub) :=
  pure [] ["n"; "m"]
    (LetIn "d" (Binop (Sub Unchecked) (Arg "n") (Arg "m"))
       (Cond (Binop Greater (Var "d") (Arg "n")) (lit 0) (Var "d"))).
#[export] Instance std_nat_max_mapping : OperationMapping (Ref Nat.max) :=
  pure ["algorithm"] ["n"; "m"] (Call "std::max" [] [Arg "n"; Arg "m"]).
#[export] Instance std_nat_min_mapping : OperationMapping (Ref Nat.min) :=
  pure ["algorithm"] ["n"; "m"] (Call "std::min" [] [Arg "n"; Arg "m"]).
#[export] Instance std_nat_eqb_mapping : OperationMapping (Ref Nat.eqb) :=
  pure [] ["n"; "m"] (Binop Equal (Arg "n") (Arg "m")).
#[export] Instance std_nat_ltb_mapping : OperationMapping (Ref Nat.ltb) :=
  pure [] ["n"; "m"] (Binop Less (Arg "n") (Arg "m")).
#[export] Instance std_nat_leb_mapping : OperationMapping (Ref Nat.leb) :=
  pure [] ["n"; "m"] (Binop LessEq (Arg "n") (Arg "m")).
#[export] Instance std_nat_compare_mapping : OperationMapping (Ref Nat.compare) :=
  pure [] ["n"; "m"]
    (Cond (Binop Less (Arg "n") (Arg "m")) (EnumValue ResultType "LT")
       (Cond (Binop Less (Arg "m") (Arg "n")) (EnumValue ResultType "GT") (EnumValue ResultType "EQ"))).

#[export] Instance std_nat_iter_mapping : OperationMapping (Ref Nat.iter) :=
  {| operation_headers := ["type_traits"; "utility"];
     operation_cpp := Expr "[](uint64_t _crane_n, auto _crane_f, auto _crane_seed) { %ret _crane_acc = std::move(_crane_seed); for (uint64_t _crane_i = 0; _crane_i < _crane_n; _crane_i++) { _crane_acc = _crane_f(std::move(_crane_acc)); } return _crane_acc; }(%arg(n), %arg(f), %arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "f"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* [PeanoNat.Nat] includes [Nat]: its [add], [mul], ... are the same
   constants, mapped above; only [eq_dec] is its own. *)
From Stdlib Require PeanoNat.

#[export] Instance std_peano_nat_eq_dec_mapping : OperationMapping (Ref PeanoNat.Nat.eq_dec) :=
  pure [] ["n"; "m"] (Binop Equal (Arg "n") (Arg "m")).


From Corelib Require Import PrimInt63.
Axiom nat_of_int : int -> nat.
#[export] Instance std_nat_of_int_mapping : OperationMapping (Ref nat_of_int) :=
  pure [] ["x0"] (Convert Exact (Int U64) (Arg "x0")).

Axiom nat_of_int_0 : nat_of_int 0 = 0%nat.
Axiom nat_of_int_pos : forall n, eqb n 0 = false -> exists m, nat_of_int n = S m.
Axiom nat_of_int_1 : nat_of_int 1 = 1%nat.
Axiom nat_of_int_gt1 : forall n, ltb 1 n = true -> exists m, nat_of_int n = S (S m).


From Corelib Require Import PrimString.
Axiom string_of_nat : nat -> string.
#[export] Instance std_string_of_nat_mapping : OperationMapping (Ref string_of_nat) :=
  pure [] ["x0"] (Call "std::to_string" [] [Arg "x0"]).
