(* SPDX-License-Identifier: BSD-3-Clause *)
(** Opt-in extraction mapping: Coq [list] -> C++ [crane::list] (an immutable,
    persistent, singly-linked cons list; see ~/crane/theories/cpp/conslist.h).

    Rationale: [cons] is the dominant list op in extracted functional code and is
    O(1) here (vs O(log n)+alloc for immer::flex_vector::push_front, ~17x slower
    in a microbenchmark).  [head]/[tail]/[drop 1] are O(1) too, which also helps
    the lexer's drop-per-char hot path.  Trade-off: [app]/[length] are O(n).

    No element boxing is needed: recursion goes through the cell's [crane::rc]
    tail, so a recursive element type (e.g. json_value containing list json_value)
    stays a bare, complete-enough field. This drops immer::box entirely. *)
From Crane Require Extraction.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Crane Extract Inductive list =>
  "crane::list<%t0>"
  [ "crane::list<%t0>{}"
    "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  Drain "%scrut.drain_each([&](auto&& _e) { %yield(std::move(_e)); });"
  From "conslist.h".

Crane Extract Inlined Constant Datatypes.length =>
  "static_cast<uint64_t>(%a0.size())" From "cstdint".

Crane Extract Inlined Constant Datatypes.app =>
  "crane::list<%t0>::app(%a0, %a1)" From "conslist.h".

Crane Extract Inlined Constant String.list_ascii_of_string =>
  "[&]() { const auto& _s = %a0; return crane::list<char>::from_range(_s.begin(), _s.end()); }()" From "conslist.h".

Crane Extract Inlined Constant String.string_of_list_ascii =>
  "[&]() { std::string _r; for (const auto& _c : %a0) _r.push_back(_c); return _r; }()" From "string".
