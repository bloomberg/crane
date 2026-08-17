(* SPDX-License-Identifier: BSD-3-Clause *)
From Crane Require Extraction.
From Crane Require Import Mapping.Std.
From Crane Require Import Mapping.NatIntStd.
From Crane Require Import Mapping.ZInt.
(* Baseline list mapping (O(N) tail copy -> O(N^2) structural recursion): *)
(* From Crane Require Import Mapping.DequeList. *)
(* cons-list mapping (crane::list): O(1) cons/tail, no element boxing.
   Replaces the immer flex_vector mapping (push_front ~17x slower on the hot
   cons path). See ~/crane/docs/codegen-perf-pass-2026-08-10.md. *)
From Crane.Libraries.ParseALot.Benchmarking Require Import ConsList.
From Crane.Libraries.ParseALot.Utils Require Import NativeMap.
From Crane.Libraries.ParseALot.Lexer.DFA Require Import IntDFA.
From Stdlib Require Import Ascii String.

From Crane.Libraries.ParseALot.Examples.PPM.Parser Require Import PPM.
From Crane.Libraries.ParseALot.Examples.JSON.Parser Require Import JSON.
From Crane.Libraries.ParseALot.Examples.Newick.Parser Require Import Newick.
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
Crane Extract Inlined Constant BinNat.N.compare =>
  "((%a0) < (%a1) ? Datatypes::Comparison::LT : (%a0) == (%a1) ? Datatypes::Comparison::EQ : Datatypes::Comparison::GT)".

(* ----------------------------------------------------------------- *)
(* Custom mapping: NativeMap -> immer::map (replaces HashTrie)         *)
(* Keyed directly on the integer position (%t0 = key type -> int64_t   *)
(* via Mapping.ZInt; %t1 = value type). immer::map's default           *)
(* std::hash<int64_t>/std::equal_to suffice, so no custom hash needed. *)
(* ----------------------------------------------------------------- *)
Crane Extract Inlined Constant NativeMap.t     => "immer::map<%t0, %t1>" From "immer/map.hpp".
Crane Extract Inlined Constant NativeMap.empty => "immer::map<%t0, %t1>{}" From "immer/map.hpp".
Crane Extract Inlined Constant NativeMap.set   => "(%a0).set(%a1, %a2)".
Crane Extract Inlined Constant NativeMap.get   =>
  "[&](){ auto _p = (%a0).find(%a1); return _p ? std::optional<%t1>(*_p) : std::optional<%t1>(); }()".

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
   has no O(1) indexing. [immer::flex_vector] gives O(1) [operator[]] and
   [size()]; [push_front] is O(log n), which is irrelevant because the matrix
   is built exactly once per lexical rule and read-only afterwards. *)
Crane Extract Inductive vec =>
  "immer::flex_vector<%t0>"
  [ "immer::flex_vector<%t0>{}"
    "%a1.push_front(%a0)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.drop(1); %br1 }"
  From "immer/flex_vector.hpp".

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
(* Separate extraction of all four parsers                            *)
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
From Crane.Libraries.ParseALot.Lexer.DFA Require Import DFA.
From Crane.Libraries.ParseALot.Lexer Require Import Regex.

Crane Guard Compare Literal.LXR.Mem.STT.TabT.R.Defs.Regexes.re_compare => Eq.

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
  lex_ppm    parse_ppm
  lex_json   parse_json
  lex_newick parse_newick
  lex_xml    parse_xml.
