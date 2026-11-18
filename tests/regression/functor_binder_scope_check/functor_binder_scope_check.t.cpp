// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <functor_binder_scope_check.h>

#include <iostream>

int main() {
  if (FunctorBinderScopeCheck::r_zero != 5) {
    std::cout << "FAIL: r_zero" << std::endl;
    return 1;
  }
  if (FunctorBinderScopeCheck::r_pos != 1) {
    std::cout << "FAIL: r_pos" << std::endl;
    return 1;
  }
  if (FunctorBinderScopeCheck::r_empty != 0) {
    std::cout << "FAIL: r_empty" << std::endl;
    return 1;
  }
  std::cout << "All functor_binder_scope_check tests passed!" << std::endl;
  return 0;
}
