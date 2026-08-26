#include <two_level_mediation.h>
#include <iostream>
int main() {
  using T = TwoLevelMediation;
  auto *p = new T::t(T::empty);
  for (unsigned i = 0; i < 300000; ++i) *p = p->wrap(i);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
