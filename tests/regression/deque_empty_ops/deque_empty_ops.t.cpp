// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Regression: DequeList map/flat_map/concat must be total on empty deques.
// Their result element type is inferred from value_type (not front()), so the
// empty cases below construct and return an empty deque rather than reading
// front() of an empty container.

#include "deque_empty_ops.h"

#include <cassert>
#include <cstdint>
#include <deque>
#include <iostream>

int main() {
  assert(DequeEmptyOps::run_map(std::deque<uint64_t>{}).empty());
  assert((DequeEmptyOps::run_map(std::deque<uint64_t>{1, 2, 3}) ==
          std::deque<uint64_t>{2, 4, 6}));

  assert(DequeEmptyOps::run_flatmap(std::deque<uint64_t>{}).empty());
  assert((DequeEmptyOps::run_flatmap(std::deque<uint64_t>{1, 2}) ==
          std::deque<uint64_t>{1, 1, 2, 2}));

  assert(DequeEmptyOps::run_concat(std::deque<std::deque<uint64_t>>{}).empty());
  assert((DequeEmptyOps::run_concat(
              std::deque<std::deque<uint64_t>>{{1, 2}, {3}}) ==
          std::deque<uint64_t>{1, 2, 3}));

  std::cout << "All deque_empty_ops tests passed!" << std::endl;
  return 0;
}
