#include <bake_functor_application_constant.h>

#include <cassert>
#include <iostream>

int main() {
  auto t = BakeFunctorApplicationConstant::total;
  std::cout << "total = " << t << std::endl;
  assert(t == 18);
  return 0;
}
