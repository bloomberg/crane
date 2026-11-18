// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <functor_binder_scope_check.h>

#include <iostream>

int main() {
  if (FunctorBinderScopeCheck::t_1 != 0) {
    std::cout << "FAIL: t_1" << std::endl;
    return 1;
  }
  std::cout << "All functor_binder_scope_check tests passed!" << std::endl;
  return 0;
}
