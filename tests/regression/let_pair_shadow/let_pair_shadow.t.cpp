#include <let_pair_shadow.h>

#include <cassert>
#include <iostream>

int main() {
  using LPS = LetPairShadow;

  // test1: map_accum running sum over [10,20,30]
  // sum([0,10,30]) + 60 = 100
  auto r1 = LPS::test1;
  std::cout << "test1 = " << r1 << " (expected 100)" << std::endl;
  assert(r1 == 100u);

  // test2: double_call_destruct 3 4 10 3
  // add_pair(3,4) = (7,12), sub_pair(10,3) = (7,13)
  // 7 + 12 + 7 + 13 = 39
  auto r2 = LPS::test2;
  std::cout << "test2 = " << r2 << " (expected 39)" << std::endl;
  assert(r2 == 39u);

  // test3: triple_call_destruct 1 2 3 4 5 6
  // add_pair(1,2)=(3,2), add_pair(3,4)=(7,12), add_pair(5,6)=(11,30)
  // 3+2+7+12+11+30 = 65
  auto r3 = LPS::test3;
  std::cout << "test3 = " << r3 << " (expected 65)" << std::endl;
  assert(r3 == 65u);

  std::cout << "All let_pair_shadow tests passed!" << std::endl;
  return 0;
}
