#include <record_mediated_drain.h>
#include <iostream>
int main() {
  using R = RecordMediatedDrain;
  auto *p = new R::t(R::empty);
  for (unsigned i = 0; i < 300000; ++i) *p = R::wrap(i, *p);
  std::cout << "built" << std::flush;
  delete p;
  std::cout << " destroyed" << std::endl;
  return 0;
}
