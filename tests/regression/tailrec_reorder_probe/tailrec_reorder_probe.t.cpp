#include <tailrec_reorder_probe.h>

#include <cassert>
#include <iostream>

int main() {
  using TRP = TailrecReorderProbe;

  // test_rev: reverse [1,2,3] = [3,2,1], sum = 6
  auto r1 = TRP::test_rev;
  std::cout << "test_rev = " << r1 << " (expected 6)" << std::endl;
  assert(r1 == 6u);

  // test_dual: dual_accum [10,20,30] nil nil
  // acc1 = [30,20,10] (reversed), sum = 60
  // acc2 = [31,21,11] (reversed, each +1), sum = 63
  // total = 123
  auto r2 = TRP::test_dual;
  std::cout << "test_dual = " << r2 << " (expected 123)" << std::endl;
  assert(r2 == 123u);

  // test_weave: weave [1,3] [2,4] nil
  // = weave [3] [4] [2,1]
  // = weave nil nil [4,3,2,1]
  // = rev_append [4,3,2,1] nil = [1,2,3,4]
  // Actually weave base case: mynil => rev_append acc l2
  // weave [1,3] [2,4] nil
  //   l1=mycons 1 [3], l2=mycons 2 [4]
  //   acc = mycons 2 (mycons 1 nil) = [2,1]
  //   weave [3] [4] [2,1]
  //   l1=mycons 3 [], l2=mycons 4 []
  //   acc = mycons 4 (mycons 3 [2,1]) = [4,3,2,1]
  //   weave [] [] [4,3,2,1]
  //   l1=mynil => rev_append [4,3,2,1] [] = [1,2,3,4]
  // sum = 10
  auto r3 = TRP::test_weave;
  std::cout << "test_weave = " << r3 << " (expected 10)" << std::endl;
  assert(r3 == 10u);

  std::cout << "All tailrec_reorder_probe tests passed!" << std::endl;
  return 0;
}
