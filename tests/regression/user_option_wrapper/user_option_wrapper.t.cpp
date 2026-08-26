#include <user_option_wrapper.h>
#include <iostream>
int main() {
  using U = UserOptionWrapper;
  auto *p = new U::t(U::empty);
  for (unsigned i = 0; i < 300000; ++i) *p = p->wrap(i);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
