#include <pair_both_recursive.h>
#include <iostream>
int main() {
  using P = PairBothRecursive;
  auto *p = new P::t(P::empty);
  for (unsigned i = 0; i < 300000; ++i) *p = P::wrap(*p);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
