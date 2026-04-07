#include <match_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using MCE = MatchClosureEscape;

  // bug_match_box: partial app of match-bound var stored in Box
  // The [&] lambda captures _args.d_a0 by reference inside std::visit.
  // When the visit returns, _args is destroyed → dangling reference.
  // Expected: sum_values (Node Leaf 10 Leaf) 99 = 10 + 99 = 109
  auto r = MCE::bug_match_box;
  std::cout << "bug_match_box = " << r << std::endl;
  assert(r == 109u);

  std::cout << "All match_closure_escape tests passed!" << std::endl;
  return 0;
}
