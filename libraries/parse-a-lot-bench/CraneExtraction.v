(* SPDX-License-Identifier: BSD-3-Clause *)
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
Crane Extract Inductive Ascii.ascii => "char"
  [ "(static_cast<char>((%a0 ? 1 : 0) | (%a1 ? 2 : 0) | (%a2 ? 4 : 0) | (%a3 ? 8 : 0) | (%a4 ? 16 : 0) | (%a5 ? 32 : 0) | (%a6 ? 64 : 0) | (%a7 ? 128 : 0)))" ]
  "bool %b0a0 = %scrut & 1; bool %b0a1 = (%scrut >> 1) & 1; bool %b0a2 = (%scrut >> 2) & 1; bool %b0a3 = (%scrut >> 3) & 1; bool %b0a4 = (%scrut >> 4) & 1; bool %b0a5 = (%scrut >> 5) & 1; bool %b0a6 = (%scrut >> 6) & 1; bool %b0a7 = (%scrut >> 7) & 1; %br0"
  From "".

(* ----------------------------------------------------------------- *)
(* Custom mapping: String.string -> std::string                       *)
(* ----------------------------------------------------------------- *)
Crane Extract Inductive String.string => "std::string"
  [ "std::string()"
    "std::string(1, %a0) + %a1" ]
  "if (%scrut.empty()) { %br0 } else { char %b1a0 = %scrut[0]; std::string %b1a1 = %scrut.substr(1); %br1 }"
  From "string".

Crane Extract Inlined Constant String.append => "%a0 + %a1".
Crane Extract Inlined Constant String.eqb => "(%a0 == %a1)".

(* ----------------------------------------------------------------- *)
(* Custom mapping: Ascii comparison via native char comparison        *)
(* ----------------------------------------------------------------- *)
Crane Extract Inlined Constant Ascii.N_of_ascii => "(static_cast<unsigned int>(static_cast<unsigned char>(%a0)))".
Crane Extract Inlined Constant Ascii.compare =>
  "((%a0) < (%a1) ? Datatypes::Comparison::LT : (%a0) == (%a1) ? Datatypes::Comparison::EQ : Datatypes::Comparison::GT)".

(* ----------------------------------------------------------------- *)
(* Custom mapping: NativeMap -> immer::map (replaces HashTrie)         *)
(* The lexer memo is keyed by a (pointer, position) pair; [crane::hash] *)
(* hashes a pair from its components' [std::hash]es.                  *)
(* ----------------------------------------------------------------- *)
Crane Extract Inlined Constant NativeMap.t     => "immer::map<%t0, %t1, crane::hash<%t0>>" From "immer/map.hpp" "crane_hash.h".
Crane Extract Inlined Constant NativeMap.empty => "immer::map<%t0, %t1, crane::hash<%t0>>{}" From "immer/map.hpp" "crane_hash.h".

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
Crane Extract Inductive vec =>
  "crane::shared_array<%t0>"
  [ "crane::shared_array<%t0>{}"
    "%a1.push_front(%a0)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.drop(1); %br1 }"
  From "shared_array.h".

Crane Extract Inlined Constant IntDFA.vec_of_list =>
  "crane::shared_array<%t0>::of_range(%a0)" From "shared_array.h".

Crane Extract Inlined Constant IntDFA.vec_nth =>
  "(static_cast<std::size_t>(%a1) < (%a0).size() ? (%a0)[static_cast<std::size_t>(%a1)] : %a2)".
(* NOTE the [255u -]: [AsciiSigma.Alphabet.SigmaEnum] is [AsciiFinite.asciiEnum
   = asciiEnumFn 256], and [asciiEnumFn (S m) = ascii_of_nat m :: asciiEnumFn m]
   builds the list in *descending* code-point order, [chr 255 ... chr 0]. So a
   character's position in the enumeration is [255 - codepoint], not [codepoint].
   Getting this backwards silently mis-indexes every column of the transition
   matrix. *)
Crane Extract Inlined Constant IntDFA.idx_of_eqb =>
  "(255u - static_cast<unsigned int>(static_cast<unsigned char>(%a1)))".

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
