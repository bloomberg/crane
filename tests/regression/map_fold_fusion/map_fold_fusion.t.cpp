// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <map_fold_fusion.h>

#include <cassert>
#include <cstdint>
#include <iostream>

template <typename A> using list = MapFoldFusion::list<A>;

static list<uint64_t> range(uint64_t lo, uint64_t hi) {
  list<uint64_t> l = list<uint64_t>::nil();
  for (uint64_t i = hi; i >= lo && i > 0; --i) {
    l = list<uint64_t>::cons(i, std::move(l));
  }
  return l;
}

int main() {
  list<uint64_t> l = range(1, 5);
  assert(MapFoldFusion::sum_succ(l) == UINT64_C(20));
  // 2 - (4 - (6 - (8 - (10 - 0)))), saturating at each step.
  assert(MapFoldFusion::alt_double(l) == UINT64_C(2));
  assert(MapFoldFusion::alt_double(range(1, 2)) == UINT64_C(0));
  assert(MapFoldFusion::alt_double(range(2, 3)) == UINT64_C(0));
  assert(MapFoldFusion::alt_double(range(3, 3)) == UINT64_C(6));
  assert(MapFoldFusion::count_big(l) == UINT64_C(3));
  assert(MapFoldFusion::sum_twice(l) == UINT64_C(30));
  assert(MapFoldFusion::sum_and_length(l) == UINT64_C(50));
  std::cout << "map_fold_fusion: ok\n";
  return 0;
}
