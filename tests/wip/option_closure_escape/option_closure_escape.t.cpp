#include <option_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using OCE = OptionClosureEscape;

  // bug_pair_clobber: pair_escape called twice.
  // p1's closure captures t1 by [&] (dangling after pair_escape returns).
  // Second pair_escape call clobbers the stack.
  // Expected if correct: sum_values(t1, 0) = 10+30+20+0 = 60
  auto r1 = OCE::bug_pair_clobber;
  std::cout << "bug_pair_clobber = " << r1 << std::endl;
  assert(r1 == 60u);

  // bug_match_pair_clobber: match_pair called twice.
  // p1's closure captures _args from visit scope (dangling).
  // Expected if correct: sum_values(Node Leaf 10 Leaf, 0) = 10
  auto r2 = OCE::bug_match_pair_clobber;
  std::cout << "bug_match_pair_clobber = " << r2 << std::endl;
  assert(r2 == 10u);

  std::cout << "All option_closure_escape tests passed!" << std::endl;
  return 0;
}
