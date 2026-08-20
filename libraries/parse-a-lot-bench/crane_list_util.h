// SPDX-License-Identifier: BSD-3-Clause
// Helpers for driving Crane's default Datatypes::List<T> (cons-list) from the
// benchmark runners, replacing the immer flex_vector interface.
#pragma once

#include <string>
#include <variant>

#include "Datatypes.h"

// Build a Datatypes::List<char> from a byte string (the lexer input).
inline Datatypes::List<char> make_char_list(const std::string &s) {
  Datatypes::List<char> acc = Datatypes::List<char>::nil();
  for (auto it = s.rbegin(); it != s.rend(); ++it)
    acc = Datatypes::List<char>::cons(*it, acc);
  return acc;
}

// Iterate a cons-list, invoking f on each element (head-first).
template <typename T, typename F>
inline void list_for_each(const Datatypes::List<T> &l, F &&f) {
  const Datatypes::List<T> *cur = &l;
  for (;;) {
    const auto *c =
        std::get_if<typename Datatypes::List<T>::Cons>(&cur->v());
    if (!c) break;
    f(c->a);
    cur = &*c->l; // deref crane::rc<List<T>> to the tail List<T>
  }
}

template <typename T>
inline long list_length(const Datatypes::List<T> &l) {
  long n = 0;
  list_for_each(l, [&](const T &) { ++n; });
  return n;
}
