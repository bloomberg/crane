(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Extraction of [N] (binary natural numbers) to [unsigned int]: the
    mappings both flavours share, selected by [NInt.v] (std) and
    [NIntBDE.v].

    Maps [positive] to [unsigned int] and [N] to [unsigned int].
    All [N] and [Pos] operations become native C++ arithmetic.

    WARNING (prototyping only): [unsigned int] is fixed-width, whereas Rocq's
    [positive] and [N] are unbounded. Addition, multiplication, successor,
    doubling, and numeral extraction wrap modulo 2^32 once a value exceeds
    [UINT_MAX], and conversions truncate — silently diverging from the proof
    model (CWE-190/CWE-681). Use this mapping only for testing/prototyping where
    values are provably in range; for security-sensitive or unbounded arithmetic
    use the arbitrary-precision GMP mappings ([Mapping.NGMP], [Mapping.ZGMP])
    instead.
*)
From Crane Require Extraction.
From Stdlib Require Import BinNat BinPos.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.
Import Crane.Cpp.

(** [positive] is an [unsigned int]: [xI p] is [2p + 1], [xO p] is [2p],
    [xH] is [1]; a match tests [1], then oddness; a numeral is an
    [unsigned int] literal. *)
Definition positive_mapping : TypeMapping positive :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "unsigned int";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews positive;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref xH;
             ctor_build := Expr "1u";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 1u";
                       case_fields := [] |} |};
          {| ctor_source := Ref xI;
             ctor_build := Expr "(2u * %a0 + 1u)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut % 2u != 0u";
                       case_fields := [(0, OwnedProjection "(%scrut - 1u) / 2u")] |} |};
          {| ctor_source := Ref xO;
             ctor_build := Expr "(2u * %a0)";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut % 2u == 0u";
                       case_fields := [(0, OwnedProjection "%scrut / 2u")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref xI; numeral_action := NumeralDoublePlusOne 0 |};
                  {| numeral_constructor := Ref xO; numeral_action := NumeralDouble 0 |};
                  {| numeral_constructor := Ref xH; numeral_action := NumeralOne |}];
               numeral_emitter := IntegerToken "" "u";
               numeral_converters := [] |} |}.

(** [N] is an [unsigned int]: [N0] is [0], [Npos p] is [p]. *)
Definition n_mapping : TypeMapping N :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "unsigned int";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews N;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref N0;
             ctor_build := Expr "0u";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut == 0u";
                       case_fields := [] |} |};
          {| ctor_source := Ref Npos;
             ctor_build := Expr "%a0";
             ctor_view :=
               Some {| view_requirement := PreferredObservation;
                       case_test := "%scrut != 0u";
                       case_fields := [(0, OwnedProjection "%scrut")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals :=
       Some {| numeral_cases :=
                 [{| numeral_constructor := Ref N0; numeral_action := NumeralZero |};
                  {| numeral_constructor := Ref Npos; numeral_action := NumeralIdentity 0 |}];
               numeral_emitter := IntegerToken "" "u";
               numeral_converters := [Ref N.of_num_uint] |} |}.

(* Pos operations *)
Definition pos_add_mapping : OperationMapping (Ref Pos.add) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Add Unchecked) (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_sub_mapping : OperationMapping (Ref Pos.sub) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Greater (Arg "x") (Arg "y")) (Binop (Sub Unchecked) (Arg "x") (Arg "y")) (IntLit U32 1));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_mul_mapping : OperationMapping (Ref Pos.mul) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Mul Unchecked) (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_succ_mapping : OperationMapping (Ref Pos.succ) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Add Unchecked) (Arg "x") (IntLit U32 1));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_pred_mapping : OperationMapping (Ref Pos.pred) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Greater (Arg "x") (IntLit U32 1)) (Binop (Sub Unchecked) (Arg "x") (IntLit U32 1)) (IntLit U32 1));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_eqb_mapping : OperationMapping (Ref Pos.eqb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "p") (Arg "q"));
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "q"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_ltb_mapping : OperationMapping (Ref Pos.ltb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Less (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_leb_mapping : OperationMapping (Ref Pos.leb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop LessEq (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_compare_mapping : OperationMapping (Ref Pos.compare) :=
  {| operation_headers := [];
     operation_cpp := Structured (three_way (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_eq_dec_mapping : OperationMapping (Ref Pos.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_min_mapping (f : Flavour) : OperationMapping (Ref Pos.min) :=
  {| operation_headers := [(flavour_algorithm f)];
     operation_cpp := Structured (Call (flavour_min f) [] [(Arg "p"); (Arg "p'")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "p'"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_max_mapping (f : Flavour) : OperationMapping (Ref Pos.max) :=
  {| operation_headers := [(flavour_algorithm f)];
     operation_cpp := Structured (Call (flavour_max f) [] [(Arg "p"); (Arg "p'")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "p'"; argument_use := Read |}]
         ReturnValue [] |}.

(* N operations *)
Definition n_add_mapping : OperationMapping (Ref N.add) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Add Unchecked) (Arg "n") (Arg "m"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_sub_mapping : OperationMapping (Ref N.sub) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop GreaterEq (Arg "n") (Arg "m")) (Binop (Sub Unchecked) (Arg "n") (Arg "m")) (IntLit U32 0));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_mul_mapping : OperationMapping (Ref N.mul) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Mul Unchecked) (Arg "n") (Arg "m"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_div_mapping : OperationMapping (Ref N.div) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Equal (Arg "b") (IntLit U32 0)) (IntLit U32 0) (Binop Div (Arg "a") (Arg "b")));
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_modulo_mapping : OperationMapping (Ref N.modulo) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Equal (Arg "b") (IntLit U32 0)) (Arg "a") (Binop Mod (Arg "a") (Arg "b")));
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |};
          {| argument_name := "b"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_succ_mapping : OperationMapping (Ref N.succ) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Add Unchecked) (Arg "n") (IntLit U32 1));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_pred_mapping : OperationMapping (Ref N.pred) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Equal (Arg "n") (IntLit U32 0)) (IntLit U32 0) (Binop (Sub Unchecked) (Arg "n") (IntLit U32 1)));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_eqb_mapping : OperationMapping (Ref N.eqb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "n") (Arg "m"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_ltb_mapping : OperationMapping (Ref N.ltb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Less (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_leb_mapping : OperationMapping (Ref N.leb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop LessEq (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_compare_mapping : OperationMapping (Ref N.compare) :=
  {| operation_headers := [];
     operation_cpp := Structured (three_way (Arg "n") (Arg "m"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_eq_dec_mapping : OperationMapping (Ref N.eq_dec) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "n") (Arg "m"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "m"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_min_mapping (f : Flavour) : OperationMapping (Ref N.min) :=
  {| operation_headers := [(flavour_algorithm f)];
     operation_cpp := Structured (Call (flavour_min f) [] [(Arg "n"); (Arg "n'")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "n'"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_max_mapping (f : Flavour) : OperationMapping (Ref N.max) :=
  {| operation_headers := [(flavour_algorithm f)];
     operation_cpp := Structured (Call (flavour_max f) [] [(Arg "n"); (Arg "n'")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "n'"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_double_mapping : OperationMapping (Ref N.double) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Mul Unchecked) (Arg "n") (IntLit U32 2));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_succ_double_mapping : OperationMapping (Ref N.succ_double) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Add Unchecked) (Binop (Mul Unchecked) (Arg "x") (IntLit U32 2)) (IntLit U32 1));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* Conversions.  A [nat] is whatever the [nat] mapping in force makes it
   ([uint64_t] under [Mapping.NatInt]), so the conversions into it name
   the type their call yields, [ResultType], rather than this mapping's width. *)
Definition n_of_nat_mapping : OperationMapping (Ref N.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert Wrap ResultType (Arg "n"));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
Definition n_to_nat_mapping : OperationMapping (Ref N.to_nat) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert Exact ResultType (Arg "a"));
     operation_contract :=
       PureOperation
         [{| argument_name := "a"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_of_nat_mapping : OperationMapping (Ref Pos.of_nat) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert Exact ResultType (Cond (Binop Equal (Arg "n") (IntLit U32 0)) (IntLit U32 1) (Arg "n")));
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.
Definition pos_to_nat_mapping : OperationMapping (Ref Pos.to_nat) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert Exact ResultType (Arg "x"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
