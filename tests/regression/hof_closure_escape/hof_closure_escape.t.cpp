#include <hof_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using HCE = HofClosureEscape;

  // hof_escape passes a [&] closure through wrap_some to Some.
  // The [&] lambda captures t by reference from hof_escape's frame.
  // Expected if correct: sum_values(t1, 0) = 10+30+20+0 = 60
  auto r = HCE::bug_hof_escape;
  std::cout << "bug_hof_escape = " << r << std::endl;
  assert(r == 60u);

  std::cout << "All hof_closure_escape tests passed!" << std::endl;
  return 0;
}
