(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Standard-library extraction mappings, strings excepted.

    Maps [option], [prod], [int63], and [float] to their C++ standard
    library equivalents ([std::optional], [std::pair], [int64_t],
    [double]), and [char63] to [int64_t] (see below), as typed mappings:
    they activate on [Import].  [Std] adds the [string] mapping.

    Sets the stdlib flavor to ["std"]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

#[export] Set Crane StdLib "std".

(** [option A] is a [std::optional] of its element's C++ type, [prod] a
    [std::pair].  Both copy at their components' cost and are read by value
    when their components are. *)
#[export] Instance std_option_mapping (A : Type) : TypeMapping (option A) :=
  {| type_headers := ["optional"; "memory"];
     type_cpp :=
       Crane.Cpp.Apply "std::optional"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element";
           component_type := FieldType (Ref (@Some A)) 0 |}];
     type_copy := CopyComponents ["element"];
     type_access := ReadOnlyValue (ReadByComponents ["element"]);
     type_views := NoViews (option A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@Some A);
             ctor_build := Expr "std::make_optional<%stored(element)>(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.has_value()";
                       case_fields := [(0, CanonicalBorrowProjection "*%scrut")] |} |};
          {| ctor_source := Ref (@None A);
             ctor_build := Expr "std::optional<%stored(element)>()";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.has_value()";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** The projections are [std::get], so a match binds the pair as a
    structured binding. *)
#[export] Instance std_pair_mapping (A B : Type) : TypeMapping (prod A B) :=
  {| type_headers := ["utility"];
     type_cpp :=
       Crane.Cpp.Apply "std::pair"
         [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "first");
          Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "second")];
     type_components :=
       [{| component_name := "first";
           component_type := FieldType (Ref (@pair A B)) 0 |};
        {| component_name := "second";
           component_type := FieldType (Ref (@pair A B)) 1 |}];
     type_copy := CopyComponents ["first"; "second"];
     type_access := ReadOnlyValue (ReadByComponents ["first"; "second"]);
     type_views := NoViews (prod A B);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@pair A B);
             ctor_build := Expr "std::make_pair(%a0, %a1)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "true";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "std::get<0>(%scrut)");
                          (1, CanonicalBorrowProjection "std::get<1>(%scrut)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** [fst] and [snd] name a component in place, a borrow of the pair: a let
    that binds one out of a pair nothing moves from binds it by [const]
    reference instead of copying it. *)
#[export] Instance std_fst_mapping : OperationMapping (Ref (@fst)) :=
  {| operation_headers := ["utility"];
     operation_cpp := Expr "%arg(p).first";
     operation_contract :=
       PureOperation [{| argument_name := "p"; argument_use := Read |}]
         (ReturnBorrowed CanonicalBorrow {| path_argument := "p"; path_components := ["first"] |}) [] |}.

#[export] Instance std_snd_mapping : OperationMapping (Ref (@snd)) :=
  {| operation_headers := ["utility"];
     operation_cpp := Expr "%arg(p).second";
     operation_contract :=
       PureOperation [{| argument_name := "p"; argument_use := Read |}]
         (ReturnBorrowed CanonicalBorrow {| path_argument := "p"; path_components := ["second"] |}) [] |}.

(** [char63] is [int] by definition: [get] reads a byte as 0..255, and
    any [int] is a [char63].  So it is [int63]'s [int64_t]; a [char] would
    read a byte at or above 128 as negative, and drop all but a byte of
    any larger value. *)
From Corelib Require Import PrimString.
#[export] Instance std_char63_mapping : TypeMapping PrimString.char63 :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "int64_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews PrimString.char63;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(* int63 primitives - int64_t with 63-bit masking.
   Arithmetic is performed in the unsigned (uint64_t) domain, where overflow is
   defined as wraparound, then masked to [0, 2^63) to match Rocq semantics and
   cast back to int64_t. Performing add/sub/mul directly on signed int64_t would
   be undefined behavior on overflow (CWE-190), even though the result is later
   masked. Bitwise ops preserve the invariant (inputs have bit 63 = 0).
   Shifts guard against UB when shift amount >= 63 and shift in the unsigned
   domain. Division and modulo by zero follow Rocq rather than C++: [x / 0]
   is 0, and [x mod 0] is [x].

   The guarded branch also has to be well-defined on its own, not merely
   unreachable: with constant arguments the compiler folds both arms of the
   conditional and diagnoses a literal division or over-wide shift even in the
   arm the guard excludes. Hence the redundant-looking [| (%arg(y) == 0)] on the
   divisor, which is the divisor itself whenever it is nonzero and 1
   otherwise, and the [& 63] on the shift count, which is the identity
   whenever the guard admits it. *)
From Corelib Require Import PrimInt63.
#[export] Instance std_int63_mapping : TypeMapping PrimInt63.int :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "int64_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews PrimInt63.int;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
#[export] Instance std_int63_add_mapping : OperationMapping (Ref PrimInt63.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) + static_cast<uint64_t>(%arg(y))) & 0x7FFFFFFFFFFFFFFFULL)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_sub_mapping : OperationMapping (Ref PrimInt63.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) - static_cast<uint64_t>(%arg(y))) & 0x7FFFFFFFFFFFFFFFULL)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_mul_mapping : OperationMapping (Ref PrimInt63.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) * static_cast<uint64_t>(%arg(y))) & 0x7FFFFFFFFFFFFFFFULL)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_div_mapping : OperationMapping (Ref PrimInt63.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) == 0 ? 0 : %arg(x) / (%arg(y) | (%arg(y) == 0)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_mod_mapping : OperationMapping (Ref PrimInt63.mod) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) == 0 ? %arg(x) : %arg(x) % (%arg(y) | (%arg(y) == 0)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_eqb_mapping : OperationMapping (Ref PrimInt63.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_ltb_mapping : OperationMapping (Ref PrimInt63.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_leb_mapping : OperationMapping (Ref PrimInt63.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_land_mapping : OperationMapping (Ref PrimInt63.land) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) & %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_lor_mapping : OperationMapping (Ref PrimInt63.lor) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) | %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_lxor_mapping : OperationMapping (Ref PrimInt63.lxor) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) ^ %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_lsl_mapping : OperationMapping (Ref PrimInt63.lsl) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) >= 63 ? 0 : static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) << (%arg(y) & 63)) & 0x7FFFFFFFFFFFFFFFULL))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_lsr_mapping : OperationMapping (Ref PrimInt63.lsr) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) >= 63 ? 0 : static_cast<int64_t>(static_cast<uint64_t>(%arg(x)) >> (%arg(y) & 63)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** The other int63 primitives follow Rocq's kernel in crane_int63.h:
    signed readings ([asr], [divs], [mods], [ltsb], [lesb], [compares]),
    the carrying arithmetic, exact products and divisions, [head0] and
    [tail0].  A pair, carry or comparison result is built at [%ret]. *)
#[export] Instance std_int63_asr_mapping : OperationMapping (Ref PrimInt63.asr) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_asr(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_mulc_mapping : OperationMapping (Ref PrimInt63.mulc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_mulc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_divs_mapping : OperationMapping (Ref PrimInt63.divs) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_divs(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_mods_mapping : OperationMapping (Ref PrimInt63.mods) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_mods(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_ltsb_mapping : OperationMapping (Ref PrimInt63.ltsb) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_ltsb(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_lesb_mapping : OperationMapping (Ref PrimInt63.lesb) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_lesb(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_addc_mapping : OperationMapping (Ref PrimInt63.addc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_addc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_addcarryc_mapping : OperationMapping (Ref PrimInt63.addcarryc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_addcarryc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_subc_mapping : OperationMapping (Ref PrimInt63.subc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_subc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_subcarryc_mapping : OperationMapping (Ref PrimInt63.subcarryc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_subcarryc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_diveucl_mapping : OperationMapping (Ref PrimInt63.diveucl) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_diveucl<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_diveucl_21_mapping : OperationMapping (Ref PrimInt63.diveucl_21) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_diveucl_21<%ret>(%arg(xh), %arg(xl), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "xh"; argument_use := Read |};
          {| argument_name := "xl"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_addmuldiv_mapping : OperationMapping (Ref PrimInt63.addmuldiv) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_addmuldiv(%arg(p), %arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_compare_mapping : OperationMapping (Ref PrimInt63.compare) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_compare<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_compares_mapping : OperationMapping (Ref PrimInt63.compares) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_compares<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_head0_mapping : OperationMapping (Ref PrimInt63.head0) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_head0(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_int63_tail0_mapping : OperationMapping (Ref PrimInt63.tail0) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_tail0(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* PrimFloat - IEEE 754 binary64 (C++ double).
   Import PrimFloat AFTER PrimInt63 so the qualified names below resolve
   unambiguously even though both modules export [add], [sub], etc. *)
From Corelib Require Import PrimFloat.
#[export] Instance std_float_mapping : TypeMapping PrimFloat.float :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Name "double";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews PrimFloat.float;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
#[export] Instance std_float_add_mapping : OperationMapping (Ref PrimFloat.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_sub_mapping : OperationMapping (Ref PrimFloat.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) - %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_mul_mapping : OperationMapping (Ref PrimFloat.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) * %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_div_mapping : OperationMapping (Ref PrimFloat.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) / %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_opp_mapping : OperationMapping (Ref PrimFloat.opp) :=
  {| operation_headers := [];
     operation_cpp := Expr "(-%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_abs_mapping : OperationMapping (Ref PrimFloat.abs) :=
  {| operation_headers := ["cmath"];
     operation_cpp := Expr "std::abs(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_sqrt_mapping : OperationMapping (Ref PrimFloat.sqrt) :=
  {| operation_headers := ["cmath"];
     operation_cpp := Expr "std::sqrt(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_eqb_mapping : OperationMapping (Ref PrimFloat.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_ltb_mapping : OperationMapping (Ref PrimFloat.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_leb_mapping : OperationMapping (Ref PrimFloat.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_of_uint63_mapping : OperationMapping (Ref PrimFloat.of_uint63) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<double>(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(* [classify]'s result is the [float_class] enum, whose constructors are
   numbered in declaration order: [PNormal], [NNormal], [PSubn], [NSubn],
   [PZero], [NZero], [PInf], [NInf], [NaN]. *)
#[export] Instance std_float_classify_mapping : OperationMapping (Ref PrimFloat.classify) :=
  {| operation_headers := ["cmath"];
     operation_cpp := Expr "[](double _x) { const int _c = std::fpclassify(_x); const int _n = std::signbit(_x) ? 1 : 0; return static_cast<%ret>(_c == FP_NAN ? 8 : (_c == FP_INFINITE ? 6 : _c == FP_ZERO ? 4 : _c == FP_SUBNORMAL ? 2 : 0) + _n); }(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** The other float primitives follow Rocq's kernel.  [compare] is the
    [float_comparison] enum in declaration order: [FEq], [FLt], [FGt],
    [FNotComparable] (a NaN). *)
#[export] Instance std_float_compare_mapping : OperationMapping (Ref PrimFloat.compare) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<%ret>(%arg(x) < %arg(y) ? 1 : %arg(x) > %arg(y) ? 2 : %arg(x) == %arg(y) ? 0 : 3)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_normfr_mantissa_mapping : OperationMapping (Ref PrimFloat.normfr_mantissa) :=
  {| operation_headers := ["cmath"; "cstdint"];
     operation_cpp :=
       Expr "(std::fabs(%arg(x)) >= 0.5 && std::fabs(%arg(x)) < 1.0 ? static_cast<std::int64_t>(std::ldexp(std::fabs(%arg(x)), 53)) : 0)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_frshiftexp_mapping : OperationMapping (Ref PrimFloat.frshiftexp) :=
  {| operation_headers := ["cmath"; "cstdint"];
     operation_cpp :=
       Expr "(std::isfinite(%arg(x)) && %arg(x) != 0.0 ? %ret{std::scalbn(%arg(x), -(std::ilogb(%arg(x)) + 1)), static_cast<std::int64_t>(std::ilogb(%arg(x))) + 2102} : %ret{%arg(x), 0})";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_ldshiftexp_mapping : OperationMapping (Ref PrimFloat.ldshiftexp) :=
  {| operation_headers := ["cmath"; "algorithm"; "cstdint"];
     operation_cpp := Expr "std::ldexp(%arg(x), static_cast<int>(std::min<std::int64_t>(%arg(e), 4202) - 2101))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "e"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_next_up_mapping : OperationMapping (Ref PrimFloat.next_up) :=
  {| operation_headers := ["cmath"; "limits"];
     operation_cpp := Expr "std::nextafter(%arg(x), std::numeric_limits<double>::infinity())";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance std_float_next_down_mapping : OperationMapping (Ref PrimFloat.next_down) :=
  {| operation_headers := ["cmath"; "limits"];
     operation_cpp := Expr "std::nextafter(%arg(x), -std::numeric_limits<double>::infinity())";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
