#include <reuse_use_after_move.h>

#include <cassert>
#include <iostream>

int main() {
  using R = ReuseUseAfterMove;

  // test1: rewrite_head([1,2,3], true) should produce [3, 2, 3]
  // because length([1,2,3]) = 3.
  // BUG: reuse optimization moves d_a1 to null before length(l)
  // accesses it -> null dereference -> crash
  auto t1 = R::test1;
  std::cout << "test1 = " << t1 << std::endl;
  assert(t1 == 3u);

  // test2: rewrite_head_sum([10,20,30], true) should produce [60, 20, 30]
  // because sum([10,20,30]) = 60.
  // Same bug: sum(l) accesses moved-from d_a1 -> crash
  auto t2 = R::test2;
  std::cout << "test2 = " << t2 << std::endl;
  assert(t2 == 60u);

  std::cout << "All reuse_use_after_move tests passed!" << std::endl;
  return 0;
}
