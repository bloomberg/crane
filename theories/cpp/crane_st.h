// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// ST arrays (theories/Monads/STMonad.v): an array is a
// std::shared_ptr<crane::array_storage<T>>, read through a
// std::span<const T> and written through a std::span<T>.  These operations
// convert between an array and a generated List: the list type is a template
// argument, so the header does not depend on how a unit names it.

#pragma once

#include <cstddef>
#include <memory>
#include <new>
#include <span>
#include <type_traits>
#include <utility>
#include <variant>

// crane::array_storage<T>: the elements of a fixed-size mutable array, one
// addressable T each, for every T.  It is what a typed mapping that hands out
// std::span views of an array stores:
// std::vector<bool> packs its elements into bits and has no bool to point
// at, so std::span<bool> cannot view it; array_storage<bool> stores bools.
//
// An array has an identity, so the storage is not copyable: the mapping
// shares it through a std::shared_ptr.  Its size is fixed at construction,
// so a view of it is invalidated only when the storage itself goes away.

namespace crane {

template <class T> class array_storage {
  T *data_ = nullptr;
  std::size_t size_ = 0;

  static T *allocate(std::size_t n) {
    return n == 0 ? nullptr : std::allocator<T>{}.allocate(n);
  }
  static void deallocate(T *p, std::size_t n) {
    if (p) {
      std::allocator<T>{}.deallocate(p, n);
    }
  }

public:
  using value_type = T;
  using size_type = std::size_t;
  using iterator = T *;
  using const_iterator = const T *;

  array_storage() = default;

  // n copies of fill.
  array_storage(std::size_t n, const T &fill) : data_(allocate(n)), size_(n) {
    try {
      std::uninitialized_fill_n(data_, n, fill);
    } catch (...) {
      deallocate(data_, n);
      throw;
    }
  }

  // n elements, element i initialised from init(i).
  template <class Init>
    requires std::is_invocable_r_v<T, Init &, std::size_t>
  array_storage(std::size_t n, Init init) : data_(allocate(n)), size_(n) {
    std::size_t i = 0;
    try {
      for (; i < n; ++i) {
        std::construct_at(data_ + i, init(i));
      }
    } catch (...) {
      std::destroy_n(data_, i);
      deallocate(data_, n);
      throw;
    }
  }

  array_storage(const array_storage &) = delete;
  array_storage &operator=(const array_storage &) = delete;

  ~array_storage() {
    std::destroy_n(data_, size_);
    deallocate(data_, size_);
  }

  T *data() noexcept { return data_; }
  const T *data() const noexcept { return data_; }
  std::size_t size() const noexcept { return size_; }
  bool empty() const noexcept { return size_ == 0; }

  T &operator[](std::size_t i) noexcept { return data_[i]; }
  const T &operator[](std::size_t i) const noexcept { return data_[i]; }

  T *begin() noexcept { return data_; }
  T *end() noexcept { return data_ + size_; }
  const T *begin() const noexcept { return data_; }
  const T *end() const noexcept { return data_ + size_; }
};

} // namespace crane

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

// The elements of an array, in order, as the list type L: read through its
// read view, std::span<const T>, or its writable view, std::span<T>.
template <class L, class T> L elems(std::span<T> array) {
  L result = L::nil();
  for (std::size_t i = array.size(); i > 0; --i) {
    result = L::cons(array[i - 1], std::move(result));
  }
  return result;
}

} // namespace crane::st
