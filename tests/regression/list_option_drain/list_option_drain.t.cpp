#include <list_option_drain.h>
#include <iostream>
int main() {
  using L = ListOptionDrain;
  auto *p = new L::t(L::empty);
  for (unsigned i = 0; i < 300000; ++i) *p = L::wrap(i, *p);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
