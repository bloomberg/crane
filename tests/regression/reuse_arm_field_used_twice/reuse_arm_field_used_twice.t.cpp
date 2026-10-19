// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <reuse_arm_field_used_twice.h>
#include <cassert>

using M = ReuseArmFieldUsedTwice;
using L = M::lst;

int main() {
  // dbl [1;2;3] = 1 :: [2;3] ++ [2;3]; pairs [1;2;3] = [1+2; 2+1; 3+0].
  assert(M::dbl_len == 5);
  assert(M::pairs_sum == 9);

  // A uniquely owned list takes the reuse arms.
  L d = M::dbl(L::cons(1, L::cons(2, L::cons(3, L::nil()))));
  assert(M::len(d) == 5);
  assert(M::sum(d) == 11);
  L p = M::pairs(L::cons(1, L::cons(2, L::cons(3, L::nil()))));
  assert(M::sum(p) == 9);
  return 0;
}
