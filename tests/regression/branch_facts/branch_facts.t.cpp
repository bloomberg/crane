// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <branch_facts.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
  using B = BranchFacts;
  assert(B::abs_diff(UINT64_C(7), UINT64_C(3)) == 4);
  assert(B::abs_diff(UINT64_C(3), UINT64_C(7)) == 4);
  assert(B::abs_diff(UINT64_MAX, UINT64_C(0)) == UINT64_MAX);
  assert(B::abs_diff(UINT64_C(0), UINT64_MAX) == UINT64_MAX);
  assert(B::abs_diff(UINT64_C(5), UINT64_C(5)) == 0);

  assert(B::pred_or_zero(UINT64_C(0)) == 0);
  assert(B::pred_or_zero(UINT64_C(1)) == 0);
  assert(B::pred_or_zero(UINT64_MAX) == UINT64_MAX - 1);

  assert(B::wrong_way(UINT64_C(3), UINT64_C(7)) == 0);
  assert(B::wrong_way(UINT64_C(7), UINT64_C(3)) == 0);
  assert(B::wrong_way(UINT64_C(4), UINT64_C(4)) == 0);

  assert(B::half(UINT64_MAX) == UINT64_MAX / 2);
  assert(B::parity(UINT64_C(7)) == 1 && B::parity(UINT64_C(0)) == 0);
  assert(B::ratio(UINT64_C(7), UINT64_C(0)) == 0);
  assert(B::rem(UINT64_C(7), UINT64_C(0)) == 7);
  assert(B::rem(UINT64_C(7), UINT64_C(4)) == 3);

  assert(B::is_small(UINT64_C(9)) && !B::is_small(UINT64_C(10)));
  std::cout << "branch_facts: ok\n";
  return 0;
}
