// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// C++ side of the typed_mapping_raw_array test: raw-pointer arrays owned by
// a region that frees them all at once.
#pragma once

#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

namespace raw_support {

// Owns every array the test allocates; releases them at exit.
struct region {
  std::vector<std::shared_ptr<void>> arrays;
  static region &instance() {
    static region r;
    return r;
  }
};

template <class T> std::vector<T> *make(std::uint64_t n, const T &x) {
  auto owned = std::make_shared<std::vector<T>>(static_cast<std::size_t>(n), x);
  std::vector<T> *p = owned.get();
  region::instance().arrays.push_back(std::move(owned));
  return p;
}

// Writes through the pointer: the vector changes, the pointer does not.
template <class T, class U>
std::vector<T> *set(std::vector<T> *a, std::uint64_t i, U &&x) {
  (*a)[static_cast<std::size_t>(i)] = static_cast<T>(x);
  return a;
}

// Reseats the caller's pointer on a fresh array of n copies of its first
// element.
template <class T> std::vector<T> *reseat(std::vector<T> *&a, std::uint64_t n) {
  a = make<T>(n, (*a)[0]);
  return a;
}

} // namespace raw_support
