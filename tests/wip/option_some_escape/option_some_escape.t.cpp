#include <option_some_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using OSE = OptionSomeEscape;

  // option_escape stores a [&] closure in Some (std::optional).
  // When the function returns, the captured parameter is destroyed.
  // Expected if correct: sum_values(t1, 0) = 10+30+20+0 = 60
  auto r = OSE::bug_option_some;
  std::cout << "bug_option_some = " << r << std::endl;
  assert(r == 60u);

  std::cout << "All option_some_escape tests passed!" << std::endl;
  return 0;
}
