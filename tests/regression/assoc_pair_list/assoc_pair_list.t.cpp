#include <assoc_pair_list.h>
#include <iostream>
int main() {
  using A = AssocPairList;
  auto *p = new A::t(A::empty);
  for (unsigned i = 0; i < 100000; ++i) *p = A::wrap(i, *p);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
