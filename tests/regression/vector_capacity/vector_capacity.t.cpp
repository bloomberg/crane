// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <vector_capacity.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  std::vector<uint64_t> v = VectorCapacity::fill(UINT64_C(1000));
  assert(v.size() == 1000 && v.front() == 1000 && v.back() == 1);
  // One reservation of exactly the count: no growth beyond it.
  assert(v.capacity() == 1000);
  assert(VectorCapacity::fill(UINT64_C(0)).empty());

  assert(VectorCapacity::fill_even(UINT64_C(10)).size() == 5);
  assert(VectorCapacity::fill_twice(UINT64_C(10)).size() == 20);
  std::vector<uint64_t> u = VectorCapacity::fill_until_five(UINT64_C(10));
  assert(u.size() == 5 && u.back() == 6);
  std::cout << "vector_capacity: ok\n";
  return 0;
}
