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

// The number of elements of an array of size n.
template <class I> std::size_t extent(const I &n) {
  return static_cast<std::size_t>(n);
}

// A fresh array holding the elements of the list xs, in order.
template <class T, class L>
std::shared_ptr<array_storage<T>> new_list_array(const L &xs) {
  std::size_t n = 0;
  for (const L *cur = &xs; cur;) {
    const auto *cell = std::get_if<typename L::Cons>(&cur->v());
    if (!cell) {
      break;
    }
    ++n;
    const auto &[head, tail] = *cell;
    cur = tail.get();
  }
  const L *cur = &xs;
  return std::make_shared<array_storage<T>>(n, [&](std::size_t) -> T {
    const auto &[head, tail] = std::get<typename L::Cons>(cur->v());
    cur = tail.get();
    return head;
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
