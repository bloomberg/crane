#include <functor_param_ctor_field.h>
#include <cassert>
#include <iostream>

using M = FunctorParamCtorField;

int main() {
  assert(M::made_depth(true) == 0);
  assert(M::made_depth(false) == 0);
  std::cout << "made_depth true = " << M::made_depth(true) << " (want 0)" << std::endl;
  return 0;
}
