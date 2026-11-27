From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
Require Import Crane.Mapping.NatInt.
From Stdlib Require Import List Ascii String.
Import ListNotations.

(** FAITHFUL repro of the parse-a-lot grammar's residual leaf-forward bug
    (now fixed).

    Every prior repro (sigt_leaf_forward_{string,topfn,dispatcher,ctor},
    sigt_leaf_list_dispatch, ...) approximated the RHS-values domain type
    with a DIRECT [match n with 0 => (string*unit) | _ => (nat*unit)]. Crane
    can partially see through such a direct match, so the fixes made for those
    repros never transferred to the real grammar. The REAL domain
    (theories/Parser/Defs.v:318) is
      [symbols_semty gamma := tuple (List.map symbol_semty gamma)]
    i.e. a FIXPOINT ([tuple], Utils.v:378) applied to a MAPPED list
    ([List.map symbol_semty gamma]), where [symbol_semty] dispatches through
    [t_semty]/[nt_semty]. Crane does NOT reduce [tuple (map symbol_semty ys)]
    to a concrete nested [prod ... unit] at translation time even when [ys] is
    a concrete literal -- it erases the whole thing to [std::any]. THAT is what
    forces the generic [crane_erase_fn([](const auto &tup){...})] lambda whose
    body destructures via [any_cast<pair<any,any>>] and then forwards a leaf
    (still [std::any]) into a concrete constructor.

    The fix: the value-type constructor argument path
    ([gen_and_wrap]/[gen_ctor_arg], translation.ml) now threads the field's
    CONCRETE C++ type as the expected type when the argument is an erased
    ([std::any]) pattern variable, so the leaf gets a final
    [any_cast<concrete>] before entering the factory (e.g.
    [Val::vstr(any_cast<string>(s))]).  Previously only the plain
    function-call path inserted that cast, so [wrap_string v] worked but a
    constructor forward [VStr s] did not.

    This repro mirrors examples/JSON/Parser/JSON.v byte-for-byte in structure:
    [tuple (map symbol_semty gamma)] domain, action returning [nt_semty x] via
    a constructor application ([VStr s] mirrors [JString s]), entries built as
    inline [@existT _ _ (nt, symbol_list) (pred, action)] literals in a
    [list grammar_entry], defined after everything is concrete. *)

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

(* Mirror Utils.tuple exactly. *)
Fixpoint tuple (xs : list Type) : Type :=
  match xs with
  | [] => unit
  | x :: xs' => prod x (tuple xs')
  end.

(* Concrete terminals/nonterminals, as in the JSON instantiation. *)
Inductive terminal := TSTRING | TINT.
Inductive nonterminal := Value.

(* Result inductive with constructors taking the leaf (mirrors json_value/JString). *)
Inductive val := VStr : string -> val | VInt : nat -> val.

Definition t_semty (a : terminal) : Type :=
  match a with TSTRING => string | TINT => nat end.
Definition nt_semty (x : nonterminal) : Type :=
  match x with Value => val end.

Inductive symbol := T : terminal -> symbol | NT : nonterminal -> symbol.
Definition symbol_semty (s : symbol) : Type :=
  match s with T a => t_semty a | NT x => nt_semty x end.

(* The essential ingredient: domain is tuple over a mapped list, NOT a direct match. *)
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

(* Entries mirror jsonGrammarEntries: action returns nt_semty via a constructor
   application forwarding the destructured leaf (VStr s mirrors JString s). *)
Definition entries : list grammar_entry :=
  [ @existT _ _
      (Value, [T TSTRING])
      (fun _ => true,
       fun tup => match tup with (s, _) => VStr s end)
  ; @existT _ _
      (Value, [T TINT])
      (fun _ => true,
       fun tup => match tup with (i, _) => VInt i end)
  ].

Definition num_entries (u : unit) : nat := List.length entries.
Crane Extraction "grammar_tuple_leaf_ctor" num_entries entries.
