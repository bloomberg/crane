From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatInt.
From Stdlib Require Import List Ascii String.
Import ListNotations.

Module CharStringMappings.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

(** [ascii] is a [char]: its eight bits are its fields. *)
#[global] Instance ascii_char_mapping : TypeMapping Ascii.ascii :=
  {| type_headers := [];
     type_cpp := Crane.Cpp.Int Crane.Cpp.Char;
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Ascii.ascii;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref Ascii.Ascii;
             ctor_build := Expr "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "true";
                       case_fields := [(0, OwnedProjection "static_cast<bool>((%scrut >> 0) & 1)"); (1, OwnedProjection "static_cast<bool>((%scrut >> 1) & 1)"); (2, OwnedProjection "static_cast<bool>((%scrut >> 2) & 1)"); (3, OwnedProjection "static_cast<bool>((%scrut >> 3) & 1)"); (4, OwnedProjection "static_cast<bool>((%scrut >> 4) & 1)"); (5, OwnedProjection "static_cast<bool>((%scrut >> 5) & 1)"); (6, OwnedProjection "static_cast<bool>((%scrut >> 6) & 1)"); (7, OwnedProjection "static_cast<bool>((%scrut >> 7) & 1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

(** [string] is a [std::string] of those characters. *)
#[global] Instance string_std_mapping : TypeMapping String.string :=
  {| type_headers := ["string"];
     type_cpp := Crane.Cpp.Name "std::string";
     type_components := [];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews String.string;
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref String.EmptyString;
             ctor_build := Expr "std::string()";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "%scrut.empty()";
                       case_fields := [] |} |};
          {| ctor_source := Ref String.String;
             ctor_build := Expr "std::string(1, %a0) + %a1";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation; case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, OwnedProjection "%scrut[0]"); (1, OwnedProjection "%scrut.substr(1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End CharStringMappings.

Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance append_mapping : OperationMapping (Ref (@String.append)) :=
  pure_cpp [] ["s1"; "s2"]
    (Structured (Binop (Add Unchecked) (Arg "s1") (Arg "s2"))).
#[global] Instance eqb_mapping : OperationMapping (Ref (@String.eqb)) :=
  pure_cpp [] ["s1"; "s2"]
    (Structured (Binop Equal (Arg "s1") (Arg "s2"))).

(** [sigt_leaf_forward_string] reproduced the case where the destructured
    leaf is forwarded into a *functor/closure parameter* whose concrete type
    is only known at template instantiation, and got fixed via
    [crane_call_erased]. This test is different: the "consumer"
    (`wrap_string : string -> bool`) is a plain TOP-LEVEL Coq function with an
    already fully concrete, statically-known signature at the point the
    literal action closure is *written* (domain `domty 0` is a concrete alias
    for `string * unit`, not behind any module abstraction) -- the erasure
    only shows up later, when a *different* piece of code (`run`) accesses the
    same closure generically through a value-dependent match on a
    runtime-varying index. This matches Parser.v's
    `find_predicate_and_action` / grammar-table shape far more closely than
    the functor version.

    This used to fail to *compile*: because the literal closure is stored via
    [existT] into an erased [std::any] field, [mark_own_param_for_pair_erasure]
    forced the lambda's self-destructure to go through
    [any_cast<pair<any,any>>], on the assumption (true for the functor case)
    that such a lambda's parameter always ends up generic/erased. Here the
    domain `domty 0` resolves to a fully *concrete* type at this literal (a
    literal index `0`, not an abstract parameter), so the lambda's C++
    parameter is rendered with its real concrete type -- and any_cast-ing an
    already-concrete pair as if it were [std::any] does not compile. Fixed by
    only forcing that rewrite when the lambda's own parameter type is
    actually erased/generic at this instantiation. *)
Definition wrap_string (s : string) : bool := String.eqb s s.

Definition domty (n : nat) : Type :=
  match n with
  | 0 => (string * unit)%type
  | _ => (nat * unit)%type
  end.

Definition prod2 : Type := (nat * list nat)%type.
Definition pred_ty (p : prod2) : Type := let (n, _) := p in domty n -> bool.
Definition act_ty (p : prod2) : Type := let (n, _) := p in domty n -> bool.
Definition psem (p : prod2) : Type := (pred_ty p * act_ty p)%type.
Definition entry : Type := { p : prod2 & psem p }.

Definition my_entry : entry :=
  existT psem (0, [])
    ((fun tup : domty 0 => let (v, _x) := tup in wrap_string v),
     (fun tup : domty 0 => let (v, _x) := tup in wrap_string v)).

Definition garg (n : nat) : domty n :=
  match n with
  | 0 => ("hi"%string, tt)
  | _ => (0, tt)
  end.

Definition run (e : entry) : bool :=
  match e with
  | existT _ (n, _) fg =>
      let (f, _g) := fg in
      if f (garg n) then true else false
  end.

Definition check (u : unit) : bool := run my_entry.
Crane Extraction "sigt_leaf_forward_topfn" check my_entry.
