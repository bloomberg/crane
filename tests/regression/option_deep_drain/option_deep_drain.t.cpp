#include <option_deep_drain.h>
#include <iostream>
int main() {
  using O = OptionDeepDrain;
  auto *p = new O::chain(O::build(300000, O::chain::link(UINT64_C(0), std::nullopt)));
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
