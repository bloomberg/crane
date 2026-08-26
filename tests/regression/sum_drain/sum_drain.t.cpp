#include <sum_drain.h>
#include <iostream>
int main() {
  using S = SumDrain;
  auto *p = new S::t(S::build(300000, S::t::n(Sum<uint64_t, S::t>::inl(UINT64_C(0)))));
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
