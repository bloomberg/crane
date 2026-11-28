(* SPDX-License-Identifier: BSD-3-Clause *)
From Crane Require Mapping.Descriptor Mapping.Cpp.
From Corelib Require PrimString.
From Stdlib Require List.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatInt.
From Crane Require Import Mapping.ZInt.
From Crane Require Import Mapping.Descriptor.
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
(* Baseline list mapping (O(N) tail copy -> O(N^2) structural recursion): *)
(* From Crane Require Import Mapping.DequeList. *)
(* cons-list mapping (crane::list): O(1) cons/tail, no element boxing.
   Replaces the immer flex_vector mapping (push_front ~17x slower on the hot
   cons path). See ~/crane/docs/codegen-perf-pass-2026-08-10.md. *)
From Crane.Libraries.ParseALot.Benchmarking Require Import ConsList.
From Crane.Libraries.ParseALot.Utils Require Import NativeMap.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import IntDFA.
From Stdlib Require Import Ascii String.

From Crane.Libraries.ParseALot.Examples.JSON.Parser Require Import JSON.
From Crane.Libraries.ParseALot.Examples.CSV.Parser Require Import CSV.
From Crane.Libraries.ParseALot.Examples.XML.Parser Require Import XML.

(* ----------------------------------------------------------------- *)
(* Custom mapping: Ascii.ascii -> char                                *)
(* ----------------------------------------------------------------- *)
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

(* ----------------------------------------------------------------- *)
(* Custom mapping: Ascii comparison via native char comparison        *)
(* ----------------------------------------------------------------- *)
#[global] Instance N_of_ascii_mapping : OperationMapping (Ref (@Ascii.N_of_ascii)) :=
  pure_cpp [] ["a"]
    (Expr "(static_cast<unsigned int>(static_cast<unsigned char>(%arg(a))))").
#[global] Instance compare_mapping : OperationMapping (Ref (@Ascii.compare)) :=
  pure_cpp [] ["a"; "b"]
    (Expr "((%arg(a)) < (%arg(b)) ? Datatypes::Comparison::LT : (%arg(a)) == (%arg(b)) ? Datatypes::Comparison::EQ : Datatypes::Comparison::GT)").

(* ----------------------------------------------------------------- *)
(* Custom mapping: NativeMap -> immer::map (replaces HashTrie)         *)
(* The lexer memo is keyed by a (pointer, position) pair; [crane::hash] *)
(* hashes a pair from its components' [std::hash]es.                  *)
(* ----------------------------------------------------------------- *)
#[global] Instance t_mapping (K V : Type) : TypeMapping (NativeMap.t K V) :=
  value_type ["immer/map.hpp"; "crane_hash.h"]
    (Apply "immer::map" [TypeArg (SourceType K); TypeArg (SourceType V);
                         TypeArg (Apply "crane::hash" [TypeArg (SourceType K)])]) UnknownCopy.
#[global] Instance empty_mapping : OperationMapping (Ref (@NativeMap.empty)) :=
  pure_cpp ["immer/map.hpp"; "crane_hash.h"] []
    (Expr "immer::map<%t0, %t1, crane::hash<%t0>>{}").

(** [get] only reads its map. *)
#[export] Instance native_map_get_mapping (K V : Type) :
  OperationMapping (Ref (@NativeMap.get K V)) :=
  {| operation_headers := ["immer/map.hpp"; "optional"; "type_traits"]%pstring;
     operation_cpp :=
       Expr "[&](){ auto _p = (%arg(m)).find(%arg(k)); using _v = std::decay_t<decltype(*_p)>; return _p ? std::optional<_v>(*_p) : std::optional<_v>(); }()"%pstring;
     operation_contract :=
       PureOperation
         [{| argument_name := "m"%pstring; argument_use := Read |};
          {| argument_name := "k"%pstring; argument_use := Read |}]
         ReturnValue [] |}.

(** [set] takes its map: at the map's last use Crane passes it as an rvalue,
    and immer's rvalue [set] then updates the map in place when nothing else
    holds it.  Where the map stays live it is passed as an lvalue, and the
    [const&] [set] copies the path as before. *)
#[export] Instance native_map_set_mapping (K V : Type) :
  OperationMapping (Ref (@NativeMap.set K V)) :=
  {| operation_headers := ["immer/map.hpp"%pstring];
     operation_cpp := Expr "(%arg(m)).set(%arg(k), %arg(v))"%pstring;
     operation_contract :=
       PureOperation
         [{| argument_name := "m"%pstring; argument_use := Take |};
          {| argument_name := "k"%pstring; argument_use := Take |};
          {| argument_name := "v"%pstring; argument_use := Take |}]
         ReturnValue [] |}.

(* ----------------------------------------------------------------- *)
(* Custom mapping: IntDFA -> O(1) flex_vector operator[] / char cast   *)
(* [dfa_nth] is the interned-DFA's list-index primitive (used for both *)
(* [matrix]/[accept] row lookups and, nested, column lookups); mapping *)
(* it directly to [operator[]] turns every DFA transition into a flat  *)
(* array index instead of the [front()+drop(1)] loop the default       *)
(* extraction of a structurally-recursive [list] walk would produce.   *)
(* [code] is the interned-DFA's column index (a character's position   *)
(* in the alphabet enumeration); since the only alphabet used anywhere *)
(* in this project is [AsciiSigma.Alphabet] (Sigma := ascii, extracted *)
(* to C++ [char]), this is equivalent to (and reuses the same trusted  *)
(* formula as) the existing [Ascii.N_of_ascii] mapping above -- see the *)
(* [Lexer.DFA.IntDFA.code] docstring for why this override is sound    *)
(* regardless of the generic (list-scan) Coq-level definition.         *)
(* ----------------------------------------------------------------- *)
(* [vec] is the interned DFA's random-access sequence (see [Lexer.DFA.IntDFA]).
   It is deliberately a *separate* inductive from [list] precisely so that it
   can be mapped to a random-access container here without disturbing the
   project-wide [list] -> [crane::list] cons-list mapping (ConsList.v), which
   has no O(1) indexing.  It is an array, as ExtractionParity.v gives OCaml:
   [crane::shared_array], immutable and shared by reference, so a copy -- a
   DFA state carries its table, and every transition and loop frame copies
   the state -- is a count bump, and [operator[]] and [size()] are O(1).  It is
   built once per lexical rule, from a list ([vec_of_list] is
   [Array.of_list] on both sides), and read-only afterwards. *)
Module VecMapping.
Import Crane.Mapping.Descriptor Crane.Mapping.Cpp.
Import PrimString.PStringNotations.
Import List.ListNotations Crane.Cpp.
Local Open Scope pstring_scope.

#[global] Instance vec_mapping (A : Type) : TypeMapping (vec A) :=
  {| type_headers := ["shared_array.h"];
     type_cpp := Crane.Cpp.Apply "crane::shared_array" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")];
     type_components :=
       [{| component_name := "element"; component_type := FieldType (Ref (@vcons A)) 0 |}];
     type_copy := UnknownCopy;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews (vec A);
     type_interface :=
       AlgebraicInterface
         [{| ctor_source := Ref (@vnil A);
             ctor_build := Expr "crane::shared_array<%stored(element)>{}";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "%scrut.empty()"; case_fields := [] |} |};
          {| ctor_source := Ref (@vcons A);
             ctor_build := Expr "%a1.push_front(%a0)";
             ctor_view :=
               Some {| view_requirement := CanonicalObservation;
                       case_test := "!%scrut.empty()";
                       case_fields :=
                         [(0, CanonicalBorrowProjection "%scrut.front()");
                          (1, OwnedProjection "%scrut.drop(1)")] |} |}];
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
End VecMapping.

#[global] Instance vec_of_list_mapping : OperationMapping (Ref (@IntDFA.vec_of_list)) :=
  pure_cpp ["shared_array.h"] ["l"]
    (Expr "crane::shared_array<%t0>::of_range(%arg(l))").

#[global] Instance vec_nth_mapping : OperationMapping (Ref (@IntDFA.vec_nth)) :=
  pure_cpp [] ["v"; "n"; "d"]
    (Expr "(static_cast<std::size_t>(%arg(n)) < (%arg(v)).size() ? (%arg(v))[static_cast<std::size_t>(%arg(n))] : %arg(d))").
(* NOTE the [255u -]: [AsciiSigma.Alphabet.SigmaEnum] is [AsciiFinite.asciiEnum
   = asciiEnumFn 256], and [asciiEnumFn (S m) = ascii_of_nat m :: asciiEnumFn m]
   builds the list in *descending* code-point order, [chr 255 ... chr 0]. So a
   character's position in the enumeration is [255 - codepoint], not [codepoint].
   Getting this backwards silently mis-indexes every column of the transition
   matrix. *)
#[global] Instance idx_of_eqb_mapping : OperationMapping (Ref (@IntDFA.idx_of_eqb)) :=
  pure_cpp [] ["eqb"; "a"]
    (Expr "(255u - static_cast<unsigned int>(static_cast<unsigned char>(%arg(a))))").

(* ----------------------------------------------------------------- *)
(* Separate extraction of all three parsers                           *)
(* ----------------------------------------------------------------- *)
Set Crane Extraction Output Directory "crane_extracted".
Set Crane Loopify.
(* Arena is intentionally OFF. `Set Crane Arena` (global) still hangs (or is
   astronomically slow) on even the smallest input after excluding every
   persistent FMapAVL/FSetAVL "Raw.tree" internal reachable from the parser
   and lexer (Cache, SllSpSet family, DFA table, regex maps/sets, lexer memo
   table, parser production/nonterminal/SLL-frame maps -- see the `Crane
   NoArena <M>.Raw.tree.` directives left in place in Regex.v, Defs.v,
   ConcreteTable.v, ConcreteMemo.v, SLLPrediction.v, all still valid and
   harmless with arena off). So the hang isn't (only) persistent-map
   sharing; something else composite-arena-specific is responsible --
   likely how deep-copy-on-escape composes when multiple arena-mode types
   are nested inside each other (regex inside DFA table inside Table inside
   ..., etc.), triggering redundant copies through several layers at once
   in a way no single-type opt-in (regex-only: slow but bounded; tree-only:
   neutral) exercises. Not diagnosed further -- would need arena-aware
   profiling/tracing of the deep-copy call graph, not further bisection by
   exclusion. Per-type opt-in remains the only verified-safe arena usage.
   See project_crane_arena_ambient memory. *)
Set Crane NonAtomicRc.
(* An inductive's values as shared one-word handles (crane::shared_variant):
   copying one is a count bump, and building a node shares its children. *)
Set Crane SharedVariant.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import DFA.
From Crane.Libraries.ParseALot.Lexer Require Import Regex.

Crane Guard Compare Literal.LXR.Mem.STT.TabT.R.Defs.Regexes.re_compare => Eq.

(* Each lexer's rules with their DFAs built, computed once here and extracted
   as data: [crane_extracted] holds the tables as constant-initialised static
   blocks rather than code building them at startup.  The bake compiles the
   lexer against the immer headers the build uses: set CRANE_BAKE_FLAGS (e.g.
   "-I$HOME/cpp/immer -DIMMER_NO_THREAD_SAFETY=1") where they are not on the
   default include path. *)
Crane Bake
  Crane.Libraries.ParseALot.Examples.JSON.Parser.JSON.json_srules
  Crane.Libraries.ParseALot.Examples.CSV.Parser.CSV.csv_srules
  Crane.Libraries.ParseALot.Examples.XML.Parser.XML.xml_srules.

(* Baseline for the codegen-perf pass: arena OFF. The retired per-type
   `Crane Arena`/`Crane Arena Shared regex` directives were removed (scoped-arena
   redesign established arena-off is fastest for parse-a-lot; see
   scoped-arena-redesign-2026-08-10.md). *)

(* SLL prediction memo-key/subparser-set comparator guards live in
   theories/Parser/SLLPrediction.v itself, inside the SllPredictionFn
   functor -- Crane extracts the functor body once as a C++ template
   (shared across all grammar instantiations), so the guard must target
   the functor-internal definition, not any single grammar's monomorphized
   copy of it. *)

Crane Separate Extraction
  lex_json parse_json
  lex_csv  parse_csv
  lex_xml  parse_xml.
