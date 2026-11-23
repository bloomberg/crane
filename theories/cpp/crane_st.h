// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// ST arrays (theories/Monads/STMonad.v): an array is a
// std::shared_ptr<crane::array_storage<T>>, read through a
// std::span<const T> and written through a std::span<T>.  These operations
// convert between an array and a generated List: the list type is a template
// argument, so the header does not depend on how a unit names it.

#pragma once

#include "array_storage.h"

#include <cstddef>
#include <memory>
#include <span>
#include <type_traits>
#include <utility>
#include <variant>

namespace crane::st {

// The number of elements of an array with bounds lo..hi, both included.
template <class I> std::size_t extent(const I &lo, const I &hi) {
  return static_cast<std::size_t>(hi - lo + 1);
}

// A fresh array of n elements, the first ones taken from the list xs in
// order; positions past the end of xs keep a value-initialised element.
template <class T, class L>
std::shared_ptr<array_storage<T>> new_list_array(std::size_t n, const L &xs) {
  const L *cur = &xs;
  return std::make_shared<array_storage<T>>(n, [&](std::size_t) -> T {
    if (cur) {
      if (const auto *cell = std::get_if<typename L::Cons>(&cur->v())) {
        const auto &[head, tail] = *cell;
        cur = tail.get();
        return head;
      }
      cur = nullptr;
    }
    return T{};
  });
}

// The elements of an array, in order, as the list type L.
template <class L, class T> L elems(std::span<const T> array) {
  L result = L::nil();
  for (std::size_t i = array.size(); i > 0; --i) {
    result = L::cons(array[i - 1], std::move(result));
  }
  return result;
}

} // namespace crane::st
