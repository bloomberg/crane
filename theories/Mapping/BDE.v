(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Bloomberg Development Environment (BDE) extraction mappings.

    Maps [option], [prod], [string], [int63], and [float] to their BDE
    equivalents ([bsl::optional], [bsl::pair], [bsl::string] with a
    [bsl::string_view] read view, [int64_t], [double]), and [char63] to
    [int64_t], as typed mappings: they activate on [Import].  The descriptors
    are [Mapping.StdCore]'s and [Mapping.Std]'s with the [bsl] spellings.

    Sets the stdlib flavor to ["BDE"]. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.
From Crane Require Import Mapping.Descriptor Mapping.Cpp.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
Local Open Scope pstring_scope.
Import Crane.Cpp.

#[export] Set Crane StdLib "BDE".

(** [option A] is a [bsl::optional] of its element's C++ type, [prod] a
    [bsl::pair].  Both copy at their components' cost and are read by value
    when their components are. *)
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

(** [fst] and [snd] name a component in place, a borrow of the pair, as in
    [Mapping.StdCore]. *)
#[export] Instance bde_fst_mapping : OperationMapping (Ref (@fst)) :=
  {| operation_headers := ["bsl_utility.h"];
     operation_cpp := Structured (Member (Arg "p") "first");
     operation_contract :=
       PureOperation [{| argument_name := "p"; argument_use := Read |}]
         (ReturnBorrowed CanonicalBorrow {| path_argument := "p"; path_components := ["first"] |}) [] |}.

(** [snd] borrows [second] the same way. *)
#[export] Instance bde_snd_mapping : OperationMapping (Ref (@snd)) :=
  {| operation_headers := ["bsl_utility.h"];
     operation_cpp := Structured (Member (Arg "p") "second");
     operation_contract :=
       PureOperation [{| argument_name := "p"; argument_use := Read |}]
         (ReturnBorrowed CanonicalBorrow {| path_argument := "p"; path_components := ["second"] |}) [] |}.

From Corelib Require Import PrimString.
(** [char63] is [int64_t], as [int63] is; see [Mapping.StdCore]. *)
#[export] Instance bde_char63_mapping : TypeMapping PrimString.char63 :=
  {| type_headers := ["bsl_cstdint.h"];
     type_cpp := Crane.Cpp.Int Crane.Cpp.I64;
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

(** [length s] is [s.size()]. *)
#[export] Instance bde_string_length_mapping : OperationMapping (Ref PrimString.length) :=
  {| operation_headers := ["bsl_cstdint.h"; "bsl_string_view.h"];
     operation_cpp := Structured (exact I64 (Method (Arg "s") "size" []));
     operation_contract :=
       PureOperation [{| argument_name := "s"; argument_use := Read |}] ReturnValue [] |}.

(** Cut to [max_length] bytes, as Rocq's. *)
#[export] Instance bde_string_cat_mapping : OperationMapping (Ref PrimString.cat) :=
  {| operation_headers := ["bsl_string.h"];
     operation_cpp := Structured (Method (Binop (Add Unchecked) (Arg "s1") (Arg "s2")) "substr" [(lit 0); (lit 16777211)]);
     operation_contract :=
       PureOperation
         [{| argument_name := "s1"; argument_use := ReadCanonical |};
          {| argument_name := "s2"; argument_use := ReadCanonical |}]
         ReturnValue [] |}.

(** [get s i] is the byte at [i] read unsigned, or 0 out of range. *)
#[export] Instance bde_string_get_mapping : OperationMapping (Ref PrimString.get) :=
  {| operation_headers := ["bsl_string_view.h"];
     operation_cpp := Structured (Cond (Binop And (Binop GreaterEq (Arg "i") (lit 0)) (Binop Less (Arg "i") (exact I64 (Method (Arg "s") "length" [])))) (exact I64 (wrap UChar (Index (Arg "s") (Arg "i")))) (IntLit I64 0));
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |};
          {| argument_name := "i"; argument_use := Read |}]
         ReturnValue [] |}.

(** [make n c] is [n] copies of [c]'s low byte, [n] clamped to
    [max_length]. *)
#[export] Instance bde_string_make_mapping : OperationMapping (Ref PrimString.make) :=
  {| operation_headers := ["bsl_string.h"; "bsl_cstdint.h"];
     operation_cpp := Structured (Build (Name "bsl::string") [to_size (Cond (Binop Less (Arg "n") (IntLit I64 16777211)) (Arg "n") (IntLit I64 16777211)); (wrap Char (wrap UChar (Binop BitAnd (Arg "c") (lit 255))))]);
     operation_contract :=
       PureOperation
         [{| argument_name := "n"; argument_use := Read |};
          {| argument_name := "c"; argument_use := Read |}]
         ReturnValue [] |}.

(** [max_length] is Rocq's bound, 16777211 (2^24 - 5). *)
#[export] Instance bde_string_max_length_mapping : OperationMapping (Ref PrimString.max_length) :=
  {| operation_headers := ["bsl_cstdint.h"];
     operation_cpp := Structured (IntLit I64 16777211);
     operation_contract := PureOperation [] ReturnValue [] |}.

(** [compare] is [bsl::string_view::compare], which orders the bytes
    unsigned, mapped to the [comparison] enum ([Eq], [Lt], [Gt]). *)
#[export] Instance bde_string_compare_mapping : OperationMapping (Ref PrimString.compare) :=
  {| operation_headers := ["bsl_string_view.h"];
     operation_cpp := Expr "[](bsl::string_view _x, bsl::string_view _y) { int _c = _x.compare(_y); return static_cast<%ret>(_c == 0 ? 0 : (_c < 0 ? 1 : 2)); }(%arg(s1), %arg(s2))";
     operation_contract :=
       PureOperation
         [{| argument_name := "s1"; argument_use := Read |};
          {| argument_name := "s2"; argument_use := Read |}]
         ReturnValue [] |}.

(** [sub s off len] is [s.substr(off, len)] as an owning string, or empty
    where [off] is past the end. *)
#[export] Instance bde_string_sub_mapping : OperationMapping (Ref PrimString.sub) :=
  {| operation_headers := ["bsl_string.h"; "bsl_string_view.h"];
     operation_cpp := Structured (Cond (Binop And (Binop GreaterEq (Arg "off") (lit 0)) (Binop LessEq (Arg "off") (exact I64 (Method (Arg "s") "length" [])))) (Build (Name "bsl::string") [(Method (Arg "s") "substr" [(Arg "off"); (Arg "len")])]) (Build (Name "bsl::string") []));
     operation_contract :=
       PureOperation
         [{| argument_name := "s"; argument_use := Read |};
          {| argument_name := "off"; argument_use := Read |};
          {| argument_name := "len"; argument_use := Read |}]
         ReturnValue [] |}.

From Corelib Require Import PrimInt63.
(** [int] is an [int64_t] holding 0 to 2^63 - 1, as in [Mapping.StdCore]. *)
#[export] Instance bde_int63_mapping : TypeMapping PrimInt63.int :=
  {| type_headers := ["bsl_cstdint.h"];
     type_cpp := Crane.Cpp.Int Crane.Cpp.I64;
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews PrimInt63.int;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
(** [add], [sub] and [mul] compute in [uint64_t], where overflow wraps
    (on [int64_t] it would be undefined, CWE-190), then mask to 63 bits.
    The bitwise operations keep bit 63 clear on their own. *)
#[export] Instance bde_int63_add_mapping : OperationMapping (Ref PrimInt63.add) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Binop BitAnd (Binop (Add Unchecked) (wrap U64 (Arg "x")) (wrap U64 (Arg "y"))) (IntLit U64 9223372036854775807)));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [sub] wraps modulo 2^63. *)
#[export] Instance bde_int63_sub_mapping : OperationMapping (Ref PrimInt63.sub) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Binop BitAnd (Binop (Sub Unchecked) (wrap U64 (Arg "x")) (wrap U64 (Arg "y"))) (IntLit U64 9223372036854775807)));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [mul] wraps modulo 2^63. *)
#[export] Instance bde_int63_mul_mapping : OperationMapping (Ref PrimInt63.mul) :=
  {| operation_headers := [];
     operation_cpp := Structured (wrap I64 (Binop BitAnd (Binop (Mul Unchecked) (wrap U64 (Arg "x")) (wrap U64 (Arg "y"))) (IntLit U64 9223372036854775807)));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [div] follows Rocq, [x / 0] being 0.  Constant folding diagnoses a
    literal division by zero even in the excluded arm, so the divisor is
    [y | (y == 0)]: [y] where nonzero, else 1. *)
#[export] Instance bde_int63_div_mapping : OperationMapping (Ref PrimInt63.div) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Equal (Arg "y") (lit 0)) (lit 0) (Binop Div (Arg "x") (Binop BitOr (Arg "y") (Binop Equal (Arg "y") (lit 0)))));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [mod] follows Rocq, [x mod 0] being [x]; the divisor is guarded as in
    [div]. *)
#[export] Instance bde_int63_mod_mapping : OperationMapping (Ref PrimInt63.mod) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop Equal (Arg "y") (lit 0)) (Arg "x") (Binop Mod (Arg "x") (Binop BitOr (Arg "y") (Binop Equal (Arg "y") (lit 0)))));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [eqb] is [==]. *)
#[export] Instance bde_int63_eqb_mapping : OperationMapping (Ref PrimInt63.eqb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [ltb] is [<], unsigned since bit 63 is clear. *)
#[export] Instance bde_int63_ltb_mapping : OperationMapping (Ref PrimInt63.ltb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Less (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [leb] is [<=], unsigned since bit 63 is clear. *)
#[export] Instance bde_int63_leb_mapping : OperationMapping (Ref PrimInt63.leb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop LessEq (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [land] is [&]. *)
#[export] Instance bde_int63_land_mapping : OperationMapping (Ref PrimInt63.land) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop BitAnd (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [lor] is [|]. *)
#[export] Instance bde_int63_lor_mapping : OperationMapping (Ref PrimInt63.lor) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop BitOr (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [lxor] is [^]. *)
#[export] Instance bde_int63_lxor_mapping : OperationMapping (Ref PrimInt63.lxor) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop BitXor (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [lsl] is 0 for a shift of 63 or more, as in Rocq, else [<<] in
    [uint64_t] masked to 63 bits; [y & 63] keeps the excluded arm free of
    an over-wide shift under constant folding. *)
#[export] Instance bde_int63_lsl_mapping : OperationMapping (Ref PrimInt63.lsl) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop GreaterEq (Arg "y") (lit 63)) (lit 0) (wrap I64 (Binop BitAnd (Binop Shl (wrap U64 (Arg "x")) (Binop BitAnd (Arg "y") (lit 63))) (IntLit U64 9223372036854775807))));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [lsr] is 0 for a shift of 63 or more, else [>>] in [uint64_t]. *)
#[export] Instance bde_int63_lsr_mapping : OperationMapping (Ref PrimInt63.lsr) :=
  {| operation_headers := [];
     operation_cpp := Structured (Cond (Binop GreaterEq (Arg "y") (lit 63)) (lit 0) (wrap I64 (Binop Shr (wrap U64 (Arg "x")) (Binop BitAnd (Arg "y") (lit 63)))));
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
     operation_cpp := Structured (Call "crane::int63_asr" [] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [mulc] is the full product as a pair of high and low words. *)
#[export] Instance bde_int63_mulc_mapping : OperationMapping (Ref PrimInt63.mulc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_mulc" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [divs] is truncating signed division; [x / 0] is 0. *)
#[export] Instance bde_int63_divs_mapping : OperationMapping (Ref PrimInt63.divs) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_divs" [] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [mods] is the signed remainder; [x mod 0] is [x]. *)
#[export] Instance bde_int63_mods_mapping : OperationMapping (Ref PrimInt63.mods) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_mods" [] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [ltsb] is [<] on the two's-complement reading. *)
#[export] Instance bde_int63_ltsb_mapping : OperationMapping (Ref PrimInt63.ltsb) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_ltsb" [] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [lesb] is [<=] on the two's-complement reading. *)
#[export] Instance bde_int63_lesb_mapping : OperationMapping (Ref PrimInt63.lesb) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_lesb" [] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [addc] is [x + y] with its carry. *)
#[export] Instance bde_int63_addc_mapping : OperationMapping (Ref PrimInt63.addc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_addc" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [addcarryc] is [x + y + 1] with its carry. *)
#[export] Instance bde_int63_addcarryc_mapping : OperationMapping (Ref PrimInt63.addcarryc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_addcarryc" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [subc] is [x - y] with its borrow. *)
#[export] Instance bde_int63_subc_mapping : OperationMapping (Ref PrimInt63.subc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_subc" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [subcarryc] is [x - y - 1] with its borrow. *)
#[export] Instance bde_int63_subcarryc_mapping : OperationMapping (Ref PrimInt63.subcarryc) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_subcarryc" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [diveucl] is the pair of quotient and remainder. *)
#[export] Instance bde_int63_diveucl_mapping : OperationMapping (Ref PrimInt63.diveucl) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_diveucl" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [diveucl_21] divides the two-word number [xh:xl] by [y]. *)
#[export] Instance bde_int63_diveucl_21_mapping : OperationMapping (Ref PrimInt63.diveucl_21) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_diveucl_21" [ResultType] [(Arg "xh"); (Arg "xl"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "xh"; argument_use := Read |};
          {| argument_name := "xl"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [addmuldiv p x y] is [x] shifted left by [p], its low bits filled from
    the top of [y]. *)
#[export] Instance bde_int63_addmuldiv_mapping : OperationMapping (Ref PrimInt63.addmuldiv) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_addmuldiv" [] [(Arg "p"); (Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "p"; argument_use := Read |};
          {| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [compare] is the unsigned three-way comparison. *)
#[export] Instance bde_int63_compare_mapping : OperationMapping (Ref PrimInt63.compare) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_compare" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [compares] is the signed three-way comparison. *)
#[export] Instance bde_int63_compares_mapping : OperationMapping (Ref PrimInt63.compares) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_compares" [ResultType] [(Arg "x"); (Arg "y")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [head0] counts leading zeros within 63 bits; 63 for 0. *)
#[export] Instance bde_int63_head0_mapping : OperationMapping (Ref PrimInt63.head0) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_head0" [] [(Arg "x")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [tail0] counts trailing zeros; 63 for 0. *)
#[export] Instance bde_int63_tail0_mapping : OperationMapping (Ref PrimInt63.tail0) :=
  {| operation_headers := ["crane_int63.h"];
     operation_cpp := Structured (Call "crane::int63_tail0" [] [(Arg "x")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.

(* Import PrimFloat after PrimInt63: both export [add], [sub], ..., and the
   names below are qualified. *)
From Corelib Require Import PrimFloat.
(** [float] is IEEE 754 binary64, C++ [double]. *)
#[export] Instance bde_float_mapping : TypeMapping PrimFloat.float :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Float64;
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews PrimFloat.float;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
(** [add] is [double] [+]. *)
#[export] Instance bde_float_add_mapping : OperationMapping (Ref PrimFloat.add) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Add Unchecked) (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [sub] is [double] [-]. *)
#[export] Instance bde_float_sub_mapping : OperationMapping (Ref PrimFloat.sub) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Sub Unchecked) (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [mul] is [double] [*]. *)
#[export] Instance bde_float_mul_mapping : OperationMapping (Ref PrimFloat.mul) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop (Mul Unchecked) (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [div] is [double] [/]: IEEE, so dividing by zero gives an infinity or
    NaN. *)
#[export] Instance bde_float_div_mapping : OperationMapping (Ref PrimFloat.div) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Div (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [opp] is unary [-], which flips the sign of 0 and NaN too. *)
#[export] Instance bde_float_opp_mapping : OperationMapping (Ref PrimFloat.opp) :=
  {| operation_headers := [];
     operation_cpp := Structured (Unop Negate (Arg "x"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [abs] is [bsl::abs]. *)
#[export] Instance bde_float_abs_mapping : OperationMapping (Ref PrimFloat.abs) :=
  {| operation_headers := ["bsl_cmath.h"];
     operation_cpp := Structured (Call "bsl::abs" [] [(Arg "x")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [sqrt] is [bsl::sqrt], correctly rounded as IEEE requires. *)
#[export] Instance bde_float_sqrt_mapping : OperationMapping (Ref PrimFloat.sqrt) :=
  {| operation_headers := ["bsl_cmath.h"];
     operation_cpp := Structured (Call "bsl::sqrt" [] [(Arg "x")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [eqb] is IEEE [==]: NaN equals nothing, and [+0 == -0]. *)
#[export] Instance bde_float_eqb_mapping : OperationMapping (Ref PrimFloat.eqb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Equal (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [ltb] is IEEE [<], false on NaN. *)
#[export] Instance bde_float_ltb_mapping : OperationMapping (Ref PrimFloat.ltb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop Less (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [leb] is IEEE [<=], false on NaN. *)
#[export] Instance bde_float_leb_mapping : OperationMapping (Ref PrimFloat.leb) :=
  {| operation_headers := [];
     operation_cpp := Structured (Binop LessEq (Arg "x") (Arg "y"));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [of_uint63] is the conversion to [double], rounding to nearest. *)
#[export] Instance bde_float_of_uint63_mapping : OperationMapping (Ref PrimFloat.of_uint63) :=
  {| operation_headers := [];
     operation_cpp := Structured (Build Float64 [(Arg "x")]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [classify]'s result is the [float_class] enum, whose constructors are
   numbered in declaration order: [PNormal], [NNormal], [PSubn], [NSubn],
   [PZero], [NZero], [PInf], [NInf], [NaN]. *)
#[export] Instance bde_float_classify_mapping : OperationMapping (Ref PrimFloat.classify) :=
  {| operation_headers := ["bsl_cmath.h"];
     operation_cpp := Expr "[](double _x) { const int _c = std::fpclassify(_x); const int _n = std::signbit(_x) ? 1 : 0; return static_cast<%ret>(_c == FP_NAN ? 8 : (_c == FP_INFINITE ? 6 : _c == FP_ZERO ? 4 : _c == FP_SUBNORMAL ? 2 : 0) + _n); }(%arg(x))";
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** The other float primitives follow Rocq's kernel, as the standard
    mapping writes them ({!Mapping.StdCore}). *)
#[export] Instance bde_float_compare_mapping : OperationMapping (Ref PrimFloat.compare) :=
  {| operation_headers := [];
     operation_cpp := Structured (Convert ToEnum ResultType (Cond (Binop Less (Arg "x") (Arg "y")) (lit 1) (Cond (Binop Greater (Arg "x") (Arg "y")) (lit 2) (Cond (Binop Equal (Arg "x") (Arg "y")) (lit 0) (lit 3)))));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "y"; argument_use := Read |}]
         ReturnValue [] |}.
(** [normfr_mantissa x] is [|x|] scaled by 2^53 as an integer where
    0.5 <= [|x|] < 1, else 0. *)
#[export] Instance bde_float_normfr_mantissa_mapping : OperationMapping (Ref PrimFloat.normfr_mantissa) :=
  {| operation_headers := ["cmath"; "cstdint"];
     operation_cpp :=
       Structured (Cond (Binop And (Binop GreaterEq (Call "std::fabs" [] [(Arg "x")]) (Verbatim "0.5")) (Binop Less (Call "std::fabs" [] [(Arg "x")]) (Verbatim "1.0"))) (exact I64 (Call "std::ldexp" [] [(Call "std::fabs" [] [(Arg "x")]); (lit 53)])) (lit 0));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [frshiftexp x] is [frexp] with the exponent offset by Rocq's [shift]
    (2101); 0, infinities and NaN give exponent 0. *)
#[export] Instance bde_float_frshiftexp_mapping : OperationMapping (Ref PrimFloat.frshiftexp) :=
  {| operation_headers := ["cmath"; "cstdint"];
     operation_cpp :=
       Structured (Cond (Binop And (Call "std::isfinite" [] [(Arg "x")]) (Binop NotEqual (Arg "x") (Verbatim "0.0"))) (Build ResultType [(Call "std::scalbn" [] [(Arg "x"); (Unop Negate (Binop (Add Unchecked) (Call "std::ilogb" [] [(Arg "x")]) (lit 1)))]); (Binop (Add Unchecked) (exact I64 (Call "std::ilogb" [] [(Arg "x")])) (lit 2102))]) (Build ResultType [(Arg "x"); (lit 0)]));
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [ldshiftexp x e] is [ldexp(x, e - 2101)], [e] capped at 4202 to keep
    it in [int]. *)
#[export] Instance bde_float_ldshiftexp_mapping : OperationMapping (Ref PrimFloat.ldshiftexp) :=
  {| operation_headers := ["cmath"; "algorithm"; "cstdint"];
     operation_cpp := Structured (Call "std::ldexp" [] [(Arg "x"); (exact I32 (Binop (Sub Unchecked) (Call "std::min" [Int I64] [(Arg "e"); (lit 4202)]) (lit 2101)))]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |};
          {| argument_name := "e"; argument_use := Read |}]
         ReturnValue [] |}.
(** [next_up] is [std::nextafter] towards +infinity. *)
#[export] Instance bde_float_next_up_mapping : OperationMapping (Ref PrimFloat.next_up) :=
  {| operation_headers := ["cmath"; "limits"];
     operation_cpp := Structured (Call "std::nextafter" [] [(Arg "x"); (Call "std::numeric_limits<double>::infinity" [] [])]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
(** [next_down] is [std::nextafter] towards -infinity. *)
#[export] Instance bde_float_next_down_mapping : OperationMapping (Ref PrimFloat.next_down) :=
  {| operation_headers := ["cmath"; "limits"];
     operation_cpp := Structured (Call "std::nextafter" [] [(Arg "x"); (Unop Negate (Call "std::numeric_limits<double>::infinity" [] []))]);
     operation_contract :=
       PureOperation
         [{| argument_name := "x"; argument_use := Read |}]
         ReturnValue [] |}.
