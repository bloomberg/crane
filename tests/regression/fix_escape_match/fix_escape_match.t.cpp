#include <fix_escape_match.h>

#include <cassert>
#include <iostream>

int main() {
  using FEM = FixEscapeMatch;

  // test_match: make_fn_from_head([10]) returns Some(add).
  // add(3) should be h + 3 = 10 + 3 = 13.
  // BUG: add captures h (pattern var d_a0) by [&]; after match IIFE
  // returns, h is a dangling reference → use-after-free.
  auto r1 = FEM::test_match;
  std::cout << "test_match = " << r1 << std::endl;
  assert(r1 == 13u);

  // test_match2: make_fn_from_pair([10, 20]) returns Some(combine).
  // combine(3) should be (a+b) + 3 = 30 + 3 = 33.
  auto r2 = FEM::test_match2;
  std::cout << "test_match2 = " << r2 << std::endl;
  assert(r2 == 33u);

  std::cout << "All fix_escape_match tests passed!" << std::endl;
  return 0;
}
