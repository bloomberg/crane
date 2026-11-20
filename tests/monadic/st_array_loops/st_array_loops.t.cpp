// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "st_array_loops.h"

#include <iostream>
#include <span>
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

static_assert(std::is_same_v<decltype(&StArrayLoops::zero_from),
                             void (*)(std::span<uint64_t>, uint64_t, uint64_t)>);
static_assert(
    std::is_same_v<decltype(&StArrayLoops::sum_from),
                   uint64_t (*)(std::span<const uint64_t>, uint64_t, uint64_t)>);

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  auto [sum, elems] = StArrayLoops::loops_list(4);
  ASSERT(sum == 4);
  ASSERT((to_vector(elems) == std::vector<uint64_t>{2, 0, 0, 2}));
  auto [big, _] = StArrayLoops::loops_list(100000);
  ASSERT(big == 2 * 99998);
  if (testStatus == 0) {
    std::cout << "All st_array_loops tests passed!" << std::endl;
  }
  return testStatus;
}
