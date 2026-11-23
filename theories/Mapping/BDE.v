(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Bloomberg Development Environment (BDE) extraction mappings.

    Maps [option], [prod], [string], [int63], and [float] to their
    BDE equivalents ([bsl::optional], [bsl::pair], [bsl::string] with a
    [bsl::string_view] read view, [int64_t], [double]), and [char63] to
    [int64_t], as typed mappings (docs/typed-mappings-design.md): they
    activate on [Import].  The descriptors are [Mapping.StdCore]'s and
    [Mapping.Std]'s with the [bsl] spellings.

    Sets the stdlib flavor to ["BDE"]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.

#[export] Set Crane StdLib "BDE".

(** [option A] is a [bsl::optional] of its element's C++ type (design
    15.2), [prod] a [bsl::pair] (design 15.3).  Both copy at their
    components' cost and are read by value when their components are. *)
#[export] Instance bde_option_mapping (A : Type) : TypeMapping (option A) :=
  {| type_headers := ["bsl_optional.h"; "bsl_memory.h"];
     type_cpp :=
       Crane.Cpp.Apply "bsl::optional"
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
             ctor_build := Expr "bsl::make_optional<%stored(element)>(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.has_value()";
                       case_fields := [(0, CanonicalBorrowProjection "*%scrut")] |} |};
          {| ctor_source := Ref (@None A);
             ctor_build := Expr "bsl::optional<%stored(element)>()";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.has_value()";
                       case_fields := [] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** The projections are [first] and [second], so a match binds the pair as a
    structured binding.  A pair is built at its declared type: under the
    C++17 ABI a BDE build uses, [bsl::make_pair] is [std::make_pair] and
    returns a [std::pair], a different type from the [bsl::pair] declared. *)
#[export] Instance bde_pair_mapping (A B : Type) : TypeMapping (prod A B) :=
  {| type_headers := ["bsl_utility.h"];
     type_cpp :=
       Crane.Cpp.Apply "bsl::pair"
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
             ctor_build := Expr "bsl::pair<%stored(first), %stored(second)>(%a0, %a1)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "true";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.first");
                          (1, CanonicalBorrowProjection "%scrut.second")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance bde_fst_mapping : OperationMapping (Ref (@fst)) :=
  {| operation_headers := ["bsl_utility.h"];
     operation_cpp := Expr "%arg(p).first";
     operation_contract :=
       PureOperation [{| argument_name := "p"; argument_use := Read |}]
         (ReturnBorrowed CanonicalBorrow {| path_argument := "p"; path_components := ["first"] |}) [] |}.

#[export] Instance bde_snd_mapping : OperationMapping (Ref (@snd)) :=
  {| operation_headers := ["bsl_utility.h"];
     operation_cpp := Expr "%arg(p).second";
     operation_contract :=
       PureOperation [{| argument_name := "p"; argument_use := Read |}]
         (ReturnBorrowed CanonicalBorrow {| path_argument := "p"; path_components := ["second"] |}) [] |}.

From Corelib Require Import PrimString.
#[export] Instance bde_char63_mapping : TypeMapping PrimString.char63 :=
  {| type_headers := ["bsl_cstdint.h"];
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

(** [bsl::string], read through [bsl::string_view], as [Mapping.Std]'s
    string mapping.  [get] and [sub] are total, as Rocq's: an index out of
    range reads the null character, an offset at or past the end gives the
    empty string (CWE-125, CWE-248). *)
#[export] Instance bde_string_mapping : TypeMapping PrimString.string :=
  {| type_headers := ["bsl_string.h"; "bsl_string_view.h"];
     type_cpp := Crane.Cpp.Name "bsl::string";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views :=
       ReadViews
         {| view_headers := ["bsl_string_view.h"];
            view_cpp := Crane.Cpp.Name "bsl::string_view";
            view_from_canonical := "bsl::string_view{%value}";
            view_escape := MaterialiseView (Expr "bsl::string{%view}") |};
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance bde_string_length_mapping : OperationMapping (Ref PrimString.length) :=
  {| operation_headers := ["bsl_cstdint.h"; "bsl_string_view.h"];
     operation_cpp := Expr "static_cast<int64_t>(%arg(s).size())";
     operation_contract :=
       PureOperation [{| argument_name := "s"; argument_use := Read |}] ReturnValue [] |}.

(** Cut to [max_length] bytes, as Rocq's ([crane::string_capped] is
    generic over the string type). *)
#[export] Instance bde_string_cat_mapping : OperationMapping (Ref PrimString.cat) :=
  {| operation_headers := ["bsl_string.h"; "crane_string.h"];
     operation_cpp := Expr "crane::string_capped(%arg(s1) + %arg(s2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s1"; argument_use := ReadCanonical |};
          {| argument_name := "s2"; argument_use := ReadCanonical |}]
         ReturnValue [] |}.

#[export] Instance bde_string_get_mapping : OperationMapping (Ref PrimString.get) :=
  {| operation_headers := ["bsl_string_view.h"];
     operation_cpp := Expr "((%arg(i) >= 0 && %arg(i) < static_cast<int64_t>(%arg(s).length())) ? static_cast<int64_t>(static_cast<unsigned char>(%arg(s)[%arg(i)])) : INT64_C(0))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance bde_string_make_mapping : OperationMapping (Ref PrimString.make) :=
  {| operation_headers := ["bsl_string.h"; "bsl_cstdint.h"];
     operation_cpp := Expr "[](int64_t _n, int64_t _c) { return bsl::string(static_cast<std::size_t>(_n < INT64_C(16777211) ? _n : INT64_C(16777211)), static_cast<char>(static_cast<unsigned char>(_c & 255))); }(%arg(n), %arg(c))";
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "c"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance bde_string_max_length_mapping : OperationMapping (Ref PrimString.max_length) :=
  {| operation_headers := ["bsl_cstdint.h"];
     operation_cpp := Expr "INT64_C(16777211)";
     operation_contract := PureOperation [] ReturnValue [] |}.

#[export] Instance bde_string_compare_mapping : OperationMapping (Ref PrimString.compare) :=
  {| operation_headers := ["bsl_string_view.h"];
     operation_cpp := Expr "[](bsl::string_view _x, bsl::string_view _y) { int _c = _x.compare(_y); return static_cast<%ret>(_c == 0 ? 0 : (_c < 0 ? 1 : 2)); }(%arg(s1), %arg(s2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s1"; argument_use := Read |};
          {| argument_name := "s2"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance bde_string_sub_mapping : OperationMapping (Ref PrimString.sub) :=
  {| operation_headers := ["bsl_string.h"; "bsl_string_view.h"];
     operation_cpp := Expr "((%arg(off) >= 0 && %arg(off) <= static_cast<int64_t>(%arg(s).length())) ? bsl::string(%arg(s).substr(%arg(off), %arg(len))) : bsl::string())";
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |};
          {| argument_name := "off"; argument_use := Read |};
          {| argument_name := "len"; argument_use := Read |}]
         ReturnValue [] |}.

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
#[export] Instance bde_int63_mapping : TypeMapping PrimInt63.int :=
  {| type_headers := ["bsl_cstdint.h"];
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
#[export] Instance bde_int63_add_mapping : OperationMapping (Ref PrimInt63.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) + static_cast<uint64_t>(%arg(y))) & 0x7FFFFFFFFFFFFFFFULL)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_sub_mapping : OperationMapping (Ref PrimInt63.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) - static_cast<uint64_t>(%arg(y))) & 0x7FFFFFFFFFFFFFFFULL)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_mul_mapping : OperationMapping (Ref PrimInt63.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) * static_cast<uint64_t>(%arg(y))) & 0x7FFFFFFFFFFFFFFFULL)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_div_mapping : OperationMapping (Ref PrimInt63.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) == 0 ? 0 : %arg(x) / (%arg(y) | (%arg(y) == 0)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_mod_mapping : OperationMapping (Ref PrimInt63.mod) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) == 0 ? %arg(x) : %arg(x) % (%arg(y) | (%arg(y) == 0)))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_eqb_mapping : OperationMapping (Ref PrimInt63.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_ltb_mapping : OperationMapping (Ref PrimInt63.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_leb_mapping : OperationMapping (Ref PrimInt63.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_land_mapping : OperationMapping (Ref PrimInt63.land) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) & %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_lor_mapping : OperationMapping (Ref PrimInt63.lor) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) | %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_lxor_mapping : OperationMapping (Ref PrimInt63.lxor) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) ^ %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_lsl_mapping : OperationMapping (Ref PrimInt63.lsl) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(y) >= 63 ? 0 : static_cast<int64_t>((static_cast<uint64_t>(%arg(x)) << (%arg(y) & 63)) & 0x7FFFFFFFFFFFFFFFULL))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_lsr_mapping : OperationMapping (Ref PrimInt63.lsr) :=
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
#[export] Instance bde_int63_asr_mapping : OperationMapping (Ref PrimInt63.asr) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_asr(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_mulc_mapping : OperationMapping (Ref PrimInt63.mulc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_mulc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_divs_mapping : OperationMapping (Ref PrimInt63.divs) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_divs(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_mods_mapping : OperationMapping (Ref PrimInt63.mods) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_mods(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_ltsb_mapping : OperationMapping (Ref PrimInt63.ltsb) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_ltsb(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_lesb_mapping : OperationMapping (Ref PrimInt63.lesb) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_lesb(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_addc_mapping : OperationMapping (Ref PrimInt63.addc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_addc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_addcarryc_mapping : OperationMapping (Ref PrimInt63.addcarryc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_addcarryc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_subc_mapping : OperationMapping (Ref PrimInt63.subc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_subc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_subcarryc_mapping : OperationMapping (Ref PrimInt63.subcarryc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_subcarryc<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_diveucl_mapping : OperationMapping (Ref PrimInt63.diveucl) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_diveucl<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_diveucl_21_mapping : OperationMapping (Ref PrimInt63.diveucl_21) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_diveucl_21<%ret>(%arg(xh), %arg(xl), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "xh"; argument_use := Read |};
          {| argument_name := "xl"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_addmuldiv_mapping : OperationMapping (Ref PrimInt63.addmuldiv) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_addmuldiv(%arg(p), %arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_compare_mapping : OperationMapping (Ref PrimInt63.compare) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_compare<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_compares_mapping : OperationMapping (Ref PrimInt63.compares) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_compares<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_head0_mapping : OperationMapping (Ref PrimInt63.head0) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Expr "crane::int63_head0(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_int63_tail0_mapping : OperationMapping (Ref PrimInt63.tail0) :=
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
#[export] Instance bde_float_mapping : TypeMapping PrimFloat.float :=
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
#[export] Instance bde_float_add_mapping : OperationMapping (Ref PrimFloat.add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) + %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_sub_mapping : OperationMapping (Ref PrimFloat.sub) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) - %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_mul_mapping : OperationMapping (Ref PrimFloat.mul) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) * %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_div_mapping : OperationMapping (Ref PrimFloat.div) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(x) / %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_opp_mapping : OperationMapping (Ref PrimFloat.opp) :=
  {| operation_headers := [];
     operation_cpp := Expr "(-%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_abs_mapping : OperationMapping (Ref PrimFloat.abs) :=
  {| operation_headers := ["bsl_cmath.h"];
     operation_cpp := Expr "bsl::abs(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_sqrt_mapping : OperationMapping (Ref PrimFloat.sqrt) :=
  {| operation_headers := ["bsl_cmath.h"];
     operation_cpp := Expr "bsl::sqrt(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_eqb_mapping : OperationMapping (Ref PrimFloat.eqb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) == %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_ltb_mapping : OperationMapping (Ref PrimFloat.ltb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) < %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_leb_mapping : OperationMapping (Ref PrimFloat.leb) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(x) <= %arg(y)";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_of_uint63_mapping : OperationMapping (Ref PrimFloat.of_uint63) :=
  {| operation_headers := [];
     operation_cpp := Expr "static_cast<double>(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(* [classify]'s result is the [float_class] enum, whose constructors are
   numbered in declaration order: [PNormal], [NNormal], [PSubn], [NSubn],
   [PZero], [NZero], [PInf], [NInf], [NaN]. *)
#[export] Instance bde_float_classify_mapping : OperationMapping (Ref PrimFloat.classify) :=
  {| operation_headers := ["bsl_cmath.h"];
     operation_cpp := Expr "[](double _x) { const int _c = std::fpclassify(_x); const int _n = std::signbit(_x) ? 1 : 0; return static_cast<%ret>(_c == FP_NAN ? 8 : (_c == FP_INFINITE ? 6 : _c == FP_ZERO ? 4 : _c == FP_SUBNORMAL ? 2 : 0) + _n); }(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** The other float primitives follow Rocq's kernel in crane_float.h. *)
#[export] Instance bde_float_compare_mapping : OperationMapping (Ref PrimFloat.compare) :=
  {| operation_headers := ["crane_float.h"];
     operation_cpp := Expr "crane::float_compare<%ret>(%arg(x), %arg(y))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_normfr_mantissa_mapping : OperationMapping (Ref PrimFloat.normfr_mantissa) :=
  {| operation_headers := ["crane_float.h"];
     operation_cpp := Expr "crane::float_normfr_mantissa(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_frshiftexp_mapping : OperationMapping (Ref PrimFloat.frshiftexp) :=
  {| operation_headers := ["crane_float.h"];
     operation_cpp := Expr "crane::float_frshiftexp<%ret>(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_ldshiftexp_mapping : OperationMapping (Ref PrimFloat.ldshiftexp) :=
  {| operation_headers := ["crane_float.h"];
     operation_cpp := Expr "crane::float_ldshiftexp(%arg(x), %arg(e))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "e"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_next_up_mapping : OperationMapping (Ref PrimFloat.next_up) :=
  {| operation_headers := ["crane_float.h"];
     operation_cpp := Expr "crane::float_next_up(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
#[export] Instance bde_float_next_down_mapping : OperationMapping (Ref PrimFloat.next_down) :=
  {| operation_headers := ["crane_float.h"];
     operation_cpp := Expr "crane::float_next_down(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
