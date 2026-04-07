#include <list_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using LCE = ListClosureEscape;

  // build_fns stores partial applications (sum_values t1, sum_values t2)
  // in a list. The lambdas capture t1/t2 by [&]. When build_fns returns,
  // t1 and t2 are destroyed → dangling references in the list elements.
  // Expected if correct: sum_values(Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf), 0) = 60
  auto r = LCE::bug_list_clobber;
  std::cout << "bug_list_clobber = " << r << std::endl;
  assert(r == 60u);

  std::cout << "All list_closure_escape tests passed!" << std::endl;
  return 0;
}
