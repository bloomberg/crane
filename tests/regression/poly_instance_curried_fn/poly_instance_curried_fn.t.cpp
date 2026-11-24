#include <poly_instance_curried_fn.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = PolyInstanceCurriedFn::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 4);
  return 0;
}
