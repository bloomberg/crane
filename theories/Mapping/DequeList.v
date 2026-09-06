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
  "[](auto _r, const auto& _s) { _r.insert(_r.end(), _s.begin(), _s.end()); return _r; }(%a0, %a1)" From "deque".

(** Higher-order list functions from the [List] module. *)
(* Result element types are derived from the deque's [value_type] and a
   [std::declval] of it, never from [%a1.front()]: on an empty deque [front()]
   is undefined behaviour, and deriving a type from it (even in an unevaluated
   [decltype]) reads as unsafe.  Using [value_type] keeps the inference total
   regardless of whether the input deque is empty (CWE-476 / CWE-125). *)
Crane Extract Inlined Constant List.map =>
  "[](auto _f, const auto& _l) { std::deque<std::decay_t<decltype(_f(std::declval<typename std::decay_t<decltype(_l)>::value_type&>()))>> _r; for (const auto& _x : _l) _r.push_back(_f(_x)); return _r; }(%a0, %a1)" From "deque" "utility" "type_traits".

Crane Extract Inlined Constant List.rev =>
  "[](auto _r) { std::reverse(_r.begin(), _r.end()); return _r; }(%a0)" From "algorithm".

Crane Extract Inlined Constant List.filter =>
  "[](auto _f, const auto& _l) { std::decay_t<decltype(_l)> _r; for (const auto& _x : _l) if (_f(_x)) _r.push_back(_x); return _r; }(%a0, %a1)" From "deque".

Crane Extract Inlined Constant List.fold_right =>
  "[](auto _f, auto _a, const auto& _l) { for (auto _it = _l.rbegin(); _it != _l.rend(); ++_it) _a = _f(*_it, _a); return _a; }(%a0, %a1, %a2)" From "deque".

Crane Extract Inlined Constant List.fold_left =>
  "[](auto _f, const auto& _l, auto _a) { for (const auto& _x : _l) _a = _f(_a, _x); return _a; }(%a0, %a1, %a2)" From "deque".

Crane Extract Inlined Constant List.forallb =>
  "[](auto _f, const auto& _l) { for (const auto& _x : _l) if (!_f(_x)) return false; return true; }(%a0, %a1)" From "deque".

Crane Extract Inlined Constant List.flat_map =>
  "[](auto _f, const auto& _l) { std::deque<typename std::decay_t<decltype(_f(std::declval<typename std::decay_t<decltype(_l)>::value_type&>()))>::value_type> _r; for (const auto& _x : _l) { auto _s = _f(_x); _r.insert(_r.end(), _s.begin(), _s.end()); } return _r; }(%a0, %a1)" From "deque" "utility" "type_traits".

Crane Extract Inlined Constant List.concat =>
  "[](const auto& _ls) { std::deque<typename std::decay_t<decltype(_ls)>::value_type::value_type> _r; for (const auto& _s : _ls) _r.insert(_r.end(), _s.begin(), _s.end()); return _r; }(%a0)" From "deque" "type_traits".

(** String <-> list conversions. *)
Crane Extract Inlined Constant String.list_ascii_of_string =>
  "[](const auto& _s) { return std::deque<char>(_s.begin(), _s.end()); }(%a0)" From "deque".

Crane Extract Inlined Constant String.string_of_list_ascii =>
  "[](const auto& _s) { return std::string(_s.begin(), _s.end()); }(%a0)" From "string".
