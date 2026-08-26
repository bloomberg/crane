#include <prod_drain.h>
#include <iostream>
int main() {
  using P = ProdDrain;
  auto *p = new P::t(P::build(300000, P::t::l()));
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
