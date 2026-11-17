// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <reuse_arm_field_order.h>
#include <cassert>

using L = ReuseArmFieldOrder::lst;

int main() {
  assert(ReuseArmFieldOrder::zeroed_len == 3);
  assert(ReuseArmFieldOrder::zeroed_sum == 0);
  assert(ReuseArmFieldOrder::kept_sum == 5);
  assert(ReuseArmFieldOrder::kept_len == 1);

  // A uniquely owned list takes the reuse arms.
  L l = L::cons(1, L::cons(2, L::cons(3, L::nil())));
  L z = ReuseArmFieldOrder::zero_heads(std::move(l));
  assert(ReuseArmFieldOrder::len(z) == 3);
  assert(ReuseArmFieldOrder::sum(z) == 0);
  L k = ReuseArmFieldOrder::keep_head(L::cons(9, L::cons(8, L::nil())));
  assert(ReuseArmFieldOrder::sum(k) == 9);
  assert(ReuseArmFieldOrder::len(k) == 1);
  return 0;
}
