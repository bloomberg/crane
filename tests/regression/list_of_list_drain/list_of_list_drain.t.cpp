#include <list_of_list_drain.h>
#include <iostream>
int main() {
  using L = ListOfListDrain;
  auto *p = new L::t(L::empty);
  for (unsigned i = 0; i < 300000; ++i) *p = p->wrap(i);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
