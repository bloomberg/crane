#include <reuse_self_cycle.h>

#include <cassert>
#include <iostream>

int main() {
  using R = ReuseSelfCycle;

  // test1: prepend_self([1, 2], true) should give length 3.
  // BUG: reuse creates a cycle (tail points to self).
  // length() enters infinite recursion -> stack overflow.
  auto t1 = R::test1;
  std::cout << "test1 = " << t1 << std::endl;
  assert(t1 == 3u);

  // test2: prepend_self([42], true) should give length 2.
  // Same cycle bug -> stack overflow.
  auto t2 = R::test2;
  std::cout << "test2 = " << t2 << std::endl;
  assert(t2 == 2u);

  std::cout << "All reuse_self_cycle tests passed!" << std::endl;
  return 0;
}
