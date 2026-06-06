(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Opt-in extraction mapping: Coq [list] -> C++ [std::deque].

    Import this module to extract Coq lists as [std::deque<T>]
    instead of the default [Datatypes::List<T>] linked-list.

    [std::deque] provides O(1) amortized push_front/push_back,
    O(1) indexed access, and cache-friendly chunked storage. *)
From Crane Require Extraction.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

(** Map the [list] inductive type to [std::deque]. *)
Crane Extract Inductive list =>
  "std::deque<%t0>"
  [ "std::deque<%t0>{}"
    "[](auto _a0, auto _a1) { _a1.push_front(_a0); return _a1; }(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const auto& %b1a0 = %scrut.front(); std::decay_t<decltype(%scrut)> %b1a1(%scrut.begin()+1, %scrut.end()); %br1 }"
  From "deque".

(** Core list functions from [Datatypes]. *)
Crane Extract Inlined Constant Datatypes.length =>
  "static_cast<uint64_t>(%a0.size())" From "cstdint".

Crane Extract Inlined Constant Datatypes.app =>
  "[&]() { auto _r = %a0; auto _s = %a1; _r.insert(_r.end(), _s.begin(), _s.end()); return _r; }()" From "deque".

(** Higher-order list functions from the [List] module. *)
Crane Extract Inlined Constant List.map =>
  "[&]() { std::deque<std::decay_t<decltype(%a0(%a1.front()))>> _r; for (const auto& _x : %a1) _r.push_back(%a0(_x)); return _r; }()" From "deque".

Crane Extract Inlined Constant List.rev =>
  "[&]() { auto _r = %a0; std::reverse(_r.begin(), _r.end()); return _r; }()" From "algorithm".

Crane Extract Inlined Constant List.filter =>
  "[&]() { std::decay_t<decltype(%a1)> _r; for (const auto& _x : %a1) if (%a0(_x)) _r.push_back(_x); return _r; }()" From "deque".

Crane Extract Inlined Constant List.fold_right =>
  "[&]() { auto _a = %a1; for (auto _it = %a2.rbegin(); _it != %a2.rend(); ++_it) _a = %a0(*_it, _a); return _a; }()" From "deque".

Crane Extract Inlined Constant List.fold_left =>
  "[&]() { auto _a = %a2; for (const auto& _x : %a1) _a = %a0(_a, _x); return _a; }()" From "deque".

Crane Extract Inlined Constant List.forallb =>
  "[&]() { for (const auto& _x : %a1) if (!%a0(_x)) return false; return true; }()" From "deque".

Crane Extract Inlined Constant List.flat_map =>
  "[&]() { std::deque<typename std::decay_t<decltype(%a0(%a1.front()))>::value_type> _r; for (const auto& _x : %a1) { auto _s = %a0(_x); _r.insert(_r.end(), _s.begin(), _s.end()); } return _r; }()" From "deque".

Crane Extract Inlined Constant List.concat =>
  "[&]() { std::deque<typename std::decay_t<decltype(%a0.front())>::value_type> _r; for (const auto& _s : %a0) _r.insert(_r.end(), _s.begin(), _s.end()); return _r; }()" From "deque".

(** String <-> list conversions. *)
Crane Extract Inlined Constant String.list_ascii_of_string =>
  "[&]() { const auto& _s = %a0; return std::deque<char>(_s.begin(), _s.end()); }()" From "deque".

Crane Extract Inlined Constant String.string_of_list_ascii =>
  "[&]() { const auto& _s = %a0; return std::string(_s.begin(), _s.end()); }()" From "string".
