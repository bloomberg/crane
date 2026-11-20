// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "st_array_helpers.h"

#include <iostream>
#include <memory>
#include <type_traits>
#include <vector>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

template <typename T> std::vector<T> to_vector(const List<T> &l) {
  std::vector<T> out;
  const List<T> *cur = &l;
  while (const auto *cell = std::get_if<typename List<T>::Cons>(&cur->v())) {
    out.push_back(cell->a);
    if (!cell->l) {
      break;
    }
    cur = cell->l.get();
  }
  return out;
}

template <typename T> List<T> from_vector(const std::vector<T> &v) {
  List<T> out = List<T>::nil();
  for (std::size_t i = v.size(); i > 0; --i) {
    out = List<T>::cons(v[i - 1], std::move(out));
  }
  return out;
}

using NatArray = std::shared_ptr<std::vector<uint64_t>>;
using BoolArray = std::shared_ptr<std::vector<bool>>;

// The helpers' signatures: the canonical handle by const reference for a
// read or a write, by value where it is kept, by reference where replaced.
static_assert(std::is_same_v<decltype(&StArrayHelpers::bump),
                             void (*)(const NatArray &, uint64_t)>);
static_assert(std::is_same_v<decltype(&StArrayHelpers::middle),
                             void (*)(const NatArray &, uint64_t)>);
static_assert(std::is_same_v<decltype(&StArrayHelpers::outer),
                             void (*)(const NatArray &)>);
static_assert(std::is_same_v<decltype(&StArrayHelpers::swap_ends),
                             void (*)(const NatArray &, uint64_t)>);
static_assert(std::is_same_v<decltype(&StArrayHelpers::pick),
                             NatArray (*)(bool, NatArray, NatArray)>);
static_assert(std::is_same_v<decltype(&StArrayHelpers::write_then_pick),
                             NatArray (*)(NatArray, NatArray)>);
static_assert(std::is_same_v<decltype(&StArrayHelpers::regrow_then_write),
                             void (*)(NatArray &, uint64_t)>);
static_assert(std::is_same_v<decltype(&StArrayHelpers::flip),
                             void (*)(const BoolArray &, uint64_t)>);

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  {
    auto r = to_vector(
        StArrayHelpers::helpers_list(from_vector<uint64_t>({1, 2, 3, 4})));
    ASSERT((r == std::vector<uint64_t>{4, 3, 42, 42}));
    std::cout << "helpers_list [1; 2; 3; 4]: " << r.size() << " elements"
              << std::endl;
  }

  {
    auto [elems, others] = StArrayHelpers::keep_list(3);
    ASSERT((to_vector(elems) == std::vector<uint64_t>{8, 7, 3}));
    ASSERT((to_vector(others) == std::vector<uint64_t>{4, 4}));
    std::cout << "keep_list 3: ok" << std::endl;
  }

  {
    auto r = to_vector(StArrayHelpers::regrow_list(3));
    ASSERT((r == std::vector<uint64_t>{3, 0, 0}));
    std::cout << "regrow_list 3: ok" << std::endl;
  }

  {
    auto r = to_vector(
        StArrayHelpers::flip_list(from_vector<bool>({true, false, true})));
    ASSERT((r == std::vector<bool>{false, false, false}));
    std::cout << "flip_list: ok" << std::endl;
  }

  {
    auto [b, elems] = StArrayHelpers::bools_filled(3);
    ASSERT(b);
    ASSERT((to_vector(elems) == std::vector<bool>{false, true, false}));
    std::cout << "bools_filled 3: ok" << std::endl;
  }

  {
    // The handle owns its vector: it is released with the last copy.
    NatArray a = std::make_shared<std::vector<uint64_t>>(4, 1);
    std::weak_ptr<std::vector<uint64_t>> w = a;
    StArrayHelpers::bump(a, 2);
    ASSERT((*a)[2] == 2);
    ASSERT(a.use_count() == 1);
    a.reset();
    ASSERT(w.expired());
  }

  if (testStatus == 0) {
    std::cout << "\nAll st_array_helpers tests passed!" << std::endl;
  }
  return testStatus;
}
