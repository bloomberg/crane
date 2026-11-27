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

Module Type SEM.
  Parameter idx : Type.
  Parameter sem : idx -> Type.
End SEM.

(** Same erased-pair-of-functions shape as sigt_prod_fn_any_lit_pair, but the
    leaf value pulled out of the nested-pair destructure (`v`) is *forwarded
    directly* into another function that expects a concrete mapped type
    (`std::string`, via `String.eqb`) rather than just being consumed
    opaquely. This mirrors XML.h's `xmlnode(nm, ...)` call, where `nm` is
    pulled out of a nested `std::any_cast<std::pair<std::any,std::any>>>`
    chain but then handed to `xmlnode` (which expects `std::string`) with no
    final `std::any_cast<std::string>`.

    This used to fail to *compile*: `eq` is itself a functor parameter whose
    domain (`S.sem a`) is abstract, so its C++ type is only concrete once the
    generated template is instantiated with the caller-supplied `String.eqb`
    lambda. Crane's `any_cast` insertion for call arguments only fires when
    the callee's parameter type can be resolved to something concrete at
    translation time ([MLmagic] + [expected_ty] threading); here it can't be
    (the domain type resolves to `std::any`/`Tany` generically), so `v` was
    passed to `eq` raw, and `eq`'s concrete (non-generic) instantiation
    rejected `std::any`. Fixed by routing such calls through the
    `crane_call_erased` runtime helper (`crane_fn.h`), which uses
    `std::function` CTAD — same trick as `crane_erase_fn` — to recover `eq`'s
    concrete parameter types at C++ instantiation time and `any_cast` each
    boxed argument accordingly. *)
Module Make (S : SEM).
  Definition dom (a : S.idx) : Type := (S.sem a * unit)%type.
  Definition prod2 : Type := (S.idx * list S.idx)%type.
  Definition pred_ty (p : prod2) : Type := let (a, _) := p in dom a -> bool.
  Definition act_ty (p : prod2) : Type := let (a, _) := p in dom a -> bool.
  Definition psem (p : prod2) : Type := (pred_ty p * act_ty p)%type.
  Definition entry : Type := { p : prod2 & psem p }.

  Definition mk_entry (a : S.idx) (eq : S.sem a -> S.sem a -> bool) : entry :=
    existT psem (a, [])
      ((fun tup : dom a => let (v, _x) := tup in eq v v),
       (fun tup : dom a => let (v, _x) := tup in eq v v)).

  Definition run (e : entry) (arg : forall a, S.sem a) : bool :=
    match e with
    | existT _ (a, _) fg =>
        let (f, _g) := fg in
        if f (arg a, tt) then true else false
    end.
End Make.

Module Inst <: SEM.
  Definition idx : Type := unit.
  Definition sem : idx -> Type := fun _ => string.
End Inst.

Module M := Make Inst.
Definition my_entry : M.entry := M.mk_entry tt String.eqb.
Definition my_arg : forall a : Inst.idx, Inst.sem a := fun _ => "hi"%string.
Definition check (u : unit) : bool := M.run my_entry my_arg.
Crane Extraction "sigt_leaf_forward_string" check my_entry my_arg.
