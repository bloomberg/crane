#include <double_option_nest.h>
#include <cassert>
#include <iostream>

// `t` recurses through `option (option t)`.  `classify_ml_self_ref` does not
// see through the doubly-nested `option`, so no iterative drain is emitted for
// `~t()` and destruction recurses once per level.
int main() {
  using D = DoubleOptionNest;
  assert(D::peek(D::wrap(3, D::wrap(4, D::empty))) == 7);

  auto *p = new D::t(D::empty);
  for (unsigned i = 0; i < 300000; ++i)
    *p = D::wrap(i, *p);
  std::cout << "built" << std::flush;
  delete p; // <-- stack overflow here
  std::cout << " destroyed" << std::endl;
  return 0;
}
