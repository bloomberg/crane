#include <pair_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using PCE = PairClosureEscape;

  // pair_escape stores a [&] closure in std::make_pair.
  // When the function returns, the captured parameter is destroyed.
  // Expected if correct: sum_values(t1, 0) = 10+30+20+0 = 60
  auto r = PCE::bug_pair_escape;
  std::cout << "bug_pair_escape = " << r << std::endl;
  assert(r == 60u);

  std::cout << "All pair_closure_escape tests passed!" << std::endl;
  return 0;
}
