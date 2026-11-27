From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatInt.
From Stdlib Require Import List Ascii String.
Import ListNotations.

(** Unlike [sigt_leaf_forward_topfn], which writes the action closure directly
    at the entry's definition site, this test routes the action through a
    SINGLE shared dispatcher function ([mk_action]) with one [match] over the
    production id -- the shape of the REAL grammar table (Parser.v/Defs.v),
    which builds every production's predicate/action via
    [production_action (p : production) : predicate_semty p * action_semty p :=
    match p with ... end] and only then stores [existT psem p
    (production_action p)] per entry.

    The consumer of the dispatched closure ([run], via [mk_action]) is generic
    over the runtime-varying index [n], so it must read the closure's domain
    ([domty n], a value-dependent alias) through the fully-erased
    representation [any_cast<pair<any,any>>].  This forced two fixes: the
    producer ([garg]) must DEEP-erase the pair components it returns into the
    value-dependent [std::any] slot (so the stored value is [pair<any,any>],
    not [pair<string,unit>]), and the [pair_wrap]/[fst]/[snd] accessors must
    not synthesize out-of-scope template parameters when casting an erased
    field.  Both producer and consumer now agree on the deep-erased
    representation. *)
Definition wrap_string (s : string) : bool := String.eqb s s.

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

(* SHARED dispatcher: one function, one match, covering all productions --
   unlike prior attempts where each entry's closure was a separate literal. *)
Definition mk_action (n : nat) : domty n -> bool :=
  match n with
  | 0 => fun tup => let (v, _x) := tup in wrap_string v
  | _ => fun tup => let (v, _x) := tup in Nat.ltb v (S v)
  end.

Definition my_entry : entry :=
  existT psem (0, []) (mk_action 0, mk_action 0).

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
Crane Extraction "sigt_leaf_forward_dispatcher" check my_entry.
