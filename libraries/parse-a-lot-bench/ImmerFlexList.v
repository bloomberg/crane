(* SPDX-License-Identifier: BSD-3-Clause *)
(** Opt-in extraction mapping: Coq [list] -> C++ [immer::flex_vector], with
    COMPLETENESS-AWARE ELEMENT WRAPPING (see ~/crane/WRAP.md).

    immer containers require a *complete* element type, but Coq lists are often
    recursive. The [Boxed Element "immer::box<%t0>"] clause tells Crane to wrap
    the element in [immer::box] *only at recursive occurrences* (element types
    that recurse through the list, e.g. [json_value]). Flat elements — [char]
    (the lexer's hot path), [bool], [string*string] — stay UNBOXED.

    - [%elem]  in the type/nil templates = the (possibly boxed) element slot;
      Crane fills it with [immer::box<T>] when [T] is recursive, else [T].
    - [%t0]/[%aN] in the match/cons templates stay bare; immer::box's implicit
      conversions (ctor from T, operator const T&) make cons/match work for both.

    Requires immer headers on the include path: -I $(HOME)/cpp/immer. *)
From Crane Require Extraction.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Crane Extract Inductive list =>
  "immer::flex_vector<%elem>"
  [ "immer::flex_vector<%elem>{}"
    "%a1.push_front(%a0)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.drop(1); %br1 }"
  Boxed Element "immer::box<%t0>"
  Drain "for (const auto& _e : %scrut) { %yield(_e); }"
  From "immer/flex_vector.hpp" "immer/box.hpp".

(** Core list functions that are element-representation-agnostic. *)
Crane Extract Inlined Constant Datatypes.length =>
  "static_cast<uint64_t>(%a0.size())" From "cstdint".

(* flex_vector concatenation is O(log N) structural and works for both boxed and
   unboxed element reps (both sides are the same flex_vector<%elem>). *)
Crane Extract Inlined Constant Datatypes.app =>
  "(%a0 + %a1)" From "immer/flex_vector.hpp".

(** String <-> list conversions. [list ascii] = [char] elements, which are never
    recursive, hence always UNBOXED [flex_vector<char>]. *)
Crane Extract Inlined Constant String.list_ascii_of_string =>
  "[&]() { const auto& _s = %a0; return immer::flex_vector<char>(_s.begin(), _s.end()); }()" From "immer/flex_vector.hpp".

Crane Extract Inlined Constant String.string_of_list_ascii =>
  "[&]() { std::string _r; for (const auto& _c : %a0) _r.push_back(_c); return _r; }()" From "string".

(* Higher-order list functions (map/rev/filter/fold_*/forallb/…) are intentionally
   NOT mapped: Crane extracts their Coq definitions recursively using the
   inductive nil/cons/match templates above, which already box-or-not per element
   type consistently. This keeps boxing logic in one place. *)
