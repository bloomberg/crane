# Provenance

This directory (`Crane.Libraries.ParseALot`) is a verified, end-to-end
lexing-and-parsing pipeline imported into the Crane repository as an example
library. It is a copy of the standalone `parse-a-lot` project; its git history
was **not** brought across. The code is licensed under the BSD 3-Clause License
(see `LICENSE` in this directory); the surrounding Crane repository is licensed
under LGPL-2.1.

## Scope

The example grammars (JSON, CSV, XML) lex **7-bit ASCII input only**: the lexer
character classes in `Lexer/RegexBuilders.v` and `Examples/*/Lexer/Literal.v`
enumerate printable ASCII, with no high-byte/UTF-8 class, so any byte ≥ 128 fails
to lex (JSON accepts Unicode only via `\uXXXX` escapes). See the "ASCII-only
scope" note in `Lexer/RegexBuilders.v`.

## Upstream projects

`parse-a-lot` combines and adapts two independently published, BSD-3-Clause
verified developments:

- **Verbatim++** — a lexer built from regular expressions compiled to a DFA via
  Brzozowski derivatives, proven sound and complete under maximal munch.
  Copyright (c) 2026, Derek Egolf.
  Upstream: https://github.com/egolf-cs/Verbatim
  Paper: https://dl.acm.org/doi/10.1145/3497775.3503694

- **CoStar++** — a parser implementing the LL(\*)/SLL(\*) adaptive prediction
  algorithms, proven sound, error-free, and complete.
  Copyright (c) 2019, Samuel Lasser.
  Upstream: https://github.com/slasser/CoStar
  Paper: https://doi.org/10.1007/978-3-031-33170-1_25

## Subtree origins

Every `.v` file carries an `SPDX-License-Identifier: BSD-3-Clause` header. The
copyright holders differ by subtree:

| Path                                | Derived from        | Copyright        |
|-------------------------------------|---------------------|------------------|
| `Lexer/`                            | Verbatim++          | Derek Egolf      |
| `Examples/*/Lexer/`                 | Verbatim++          | Derek Egolf      |
| `Parser/`                           | CoStar++            | Samuel Lasser    |
| `Examples/*/Parser/`                | CoStar++            | Samuel Lasser    |
| `Utils/`                            | shared / adapted    | Egolf & Lasser   |

Files that are new to `parse-a-lot` (i.e. not present in either upstream) sit
under the same BSD-3-Clause terms. The most substantial additions are in the
integer-interned DFA layer:

- `Lexer/DFA/CanonNF.v` — a canonical-normal-form theory for regexes and the
  `Superset` closed universe.
- `Lexer/DFA/IntDFA.v` — the interned (`N`-indexed) DFA, its saturation-based
  closure argument, and the top-level correctness theorem.
- `Lexer/Memo/IntLexer.v` — the interned `State` instance; its two former
  trust-boundary axioms are now proved.
- Additions to `Lexer/DFA/Table.v` (`FillClosure`) and
  `Lexer/DFA/ConcreteTable.v` (the strengthened table interface).

## Dependencies

Beyond the Rocq standard library and the Crane plugin, this library requires:

- **CoLoR** (`coq-color`) — used by the CoStar++ parser
  (`CoLoR.Util.FGraph.TransClos`).

The optional C++ extraction paths additionally map Coq `list` onto
`crane::list` / immer containers; see the benchmarking harness under
`libraries/parse-a-lot-bench/` (a self-contained sub-project, excluded from the
crane build, with its own `README.md`, `Makefile`, `_CoqProject`, and OCaml/C++
runners plus the extraction drivers `Extraction.v` / `CraneExtraction.v`).
