// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// ST arrays (theories/Monads/STMonad.v): an array is a
// std::shared_ptr<std::vector<T>>.  These two operations convert between an
// array and a generated List: the list type is a template argument, so the
// header does not depend on how a unit names it.

#pragma once

#include <cstddef>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

namespace crane::st {

// The number of elements of an array with bounds lo..hi, both included.
template <class I> std::size_t extent(const I &lo, const I &hi) {
  return static_cast<std::size_t>(hi - lo + 1);
}

// A fresh array of n elements, the first ones taken from the list xs in
// order; positions past the end of xs keep a value-initialised element.
template <class T, class L>
std::shared_ptr<std::vector<T>> new_list_array(std::size_t n, const L &xs) {
  auto array = std::make_shared<std::vector<T>>(n);
  const L *cur = &xs;
  for (std::size_t i = 0; i < n && cur; ++i) {
    const auto *cell = std::get_if<typename L::Cons>(&cur->v());
    if (!cell) {
      break;
    }
    const auto &[head, tail] = *cell;
    (*array)[i] = head;
    cur = tail.get();
  }
  return array;
}

// The elements of an array, in order, as the list type L.
template <class L, class T>
L elems(const std::shared_ptr<std::vector<T>> &array) {
  L result = L::nil();
  for (std::size_t i = array->size(); i > 0; --i) {
    result = L::cons((*array)[i - 1], std::move(result));
  }
  return result;
}

} // namespace crane::st
