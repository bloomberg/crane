// Members of mutual groups that cannot loop on their own calls: ja reaches
// its partner only through a closure, and in the three-way cycle each call is
// an operand, so no member's body calls itself once its partners are inlined.
// Extracted under CRANE_CHECK_IR, which used to reject the recursion plan.
#include "loopify_member_own_calls.h"

#include <cassert>
#include <iostream>

int main() {
  using M = LoopifyMemberOwnCalls;
  assert(M::ja(3) == 4);
  assert(M::ja(5) == 16);
  assert(M::jb(4, 1) == 5);
  assert(M::f1(5) == 9);
  assert(M::f2(5) == 11);
  assert(M::f3(5) == 10);
  assert(M::f1(1000) == 1999);
  std::cout << "loopify_member_own_calls: ja(5)=" << M::ja(5)
            << " f1(1000)=" << M::f1(1000) << " PASSED" << std::endl;
  return 0;
}
