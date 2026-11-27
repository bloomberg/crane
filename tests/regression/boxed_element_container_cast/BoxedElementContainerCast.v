From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatInt.
From Stdlib Require Import List Ascii String.
Import ListNotations.

(** A container cast into a callee generic over the element, over a list
    mapped with a [Boxed Element] wrapper.

    [val] recurses through [list], so [list (string * val)] is
    [crane::list<crane::box<std::pair<std::string, Val>>>] wherever it is
    written.  The predicate below hands an erased [list (string * val)] to
    [nodupKeys], a function template over [list (string * A)] whose own
    declaration never boxes its element (a bare type variable never recurses).
    The cast that recovers the argument must therefore name the element
    unboxed, as the declaration does, or template argument deduction fails;
    the action hands the same leaf to [VAssoc]'s concrete factory, whose cast
    keeps the box.  [run_entry] and [action_size] run both. *)
Module BoxedElementContainerCast.

Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

Inductive val :=
| VAssoc : list (string * val) -> val
| VList : list val -> val
| VNull : val
| VStr : string -> val.

Definition nodupKeys {A : Type} (prs : list (string * A)) : bool :=
  match prs with
  | [] => true
  | _ => false
  end.

Inductive terminal := TSTRING.
Inductive nonterminal := Value | Obj.

Definition t_semty (a : terminal) : Type := match a with TSTRING => string end.
Definition nt_semty (x : nonterminal) : Type :=
  match x with
  | Value => val
  | Obj => list (string * val)
  end.

Inductive symbol := T : terminal -> symbol | NT : nonterminal -> symbol.
Definition symbol_semty (s : symbol) : Type :=
  match s with T a => t_semty a | NT x => nt_semty x end.
Definition symbols_semty (gamma : list symbol) : Type :=
  tuple (List.map symbol_semty gamma).

Definition production := (nonterminal * list symbol)%type.
Definition predicate_semty (p : production) : Type :=
  let (_, ys) := p in symbols_semty ys -> bool.
Definition action_semty (p : production) : Type :=
  let (x, ys) := p in symbols_semty ys -> nt_semty x.
Definition production_semty (p : production) : Type :=
  (predicate_semty p * action_semty p)%type.
Definition grammar_entry : Type := { p : production & production_semty p }.

Definition entries : list grammar_entry :=
  [ @existT _ _
      (Value, [NT Obj])
      (fun tup => match tup with (prs, _) => nodupKeys prs end,
       fun tup => match tup with (prs, _) => VAssoc prs end)
  ; @existT _ _
      (Value, [T TSTRING])
      (fun _ => true,
       fun tup => match tup with (s, _) => VStr s end)
  ].

Definition sample_t (a : terminal) : t_semty a :=
  match a with TSTRING => "s"%string end.
Definition sample_nt (x : nonterminal) : nt_semty x :=
  match x with
  | Value => VNull
  | Obj => [("k"%string, VNull); ("l"%string, VNull)]
  end.
Definition sample_symbol (s : symbol) : symbol_semty s :=
  match s with T a => sample_t a | NT x => sample_nt x end.
Fixpoint sample_symbols (ys : list symbol) : symbols_semty ys :=
  match ys with
  | [] => tt
  | y :: ys' => (sample_symbol y, sample_symbols ys')
  end.

Definition run_entry (e : grammar_entry) : bool :=
  match e with
  | existT _ (_, ys) (pr, _) => pr (sample_symbols ys)
  end.

Definition size_of (x : nonterminal) : nt_semty x -> nat :=
  match x return nt_semty x -> nat with
  | Value => fun v => match v with VAssoc l => List.length l | VStr _ => 100 | _ => 0 end
  | Obj => fun l => List.length l
  end.

Definition action_size (e : grammar_entry) : nat :=
  match e with
  | existT _ (x, ys) (_, act) => size_of x (act (sample_symbols ys))
  end.

Definition predicates : list bool := map run_entry entries.
Definition action_sizes : list nat := map action_size entries.

End BoxedElementContainerCast.

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

Module ListMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance list_mapping (A : Type) : TypeMapping (list A) :=
  {| type_headers := ["conslist.h"];
     type_cpp := Crane.Cpp.Apply "crane::list" [Crane.Cpp.TypeArg (Crane.Cpp.BoxedComponent "element" (Crane.Cpp.Apply "crane::box" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")]))];
     type_components :=
       [{| component_name := "element"; component_type := FieldType (Ref (@cons A)) 0 |}];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (list A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@nil A);
             ctor_build := Expr "crane::list<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@cons A);
             ctor_build := Expr "crane::cons(%a0, %a1)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%scrut.tail()")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End ListMapping.

Crane Extraction "boxed_element_container_cast" BoxedElementContainerCast.
