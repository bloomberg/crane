#include <triple_list_drain.h>
#include <iostream>
int main() {
  using T = TripleListDrain;
  auto *p = new T::t(T::empty);
  for (unsigned i = 0; i < 300000; ++i) *p = T::wrap(i, *p);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
