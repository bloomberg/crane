// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <nested_binder_scope_check.h>

#include <cstdint>
#include <iostream>

#define M NestedBinderScopeCheck

int main() {
  int fails = 0;
  auto p = M::f(5);
  if (!(p.px == 5)) { std::cout << "FAIL: p.px" << std::endl; ++fails; }
  if (!(p.py == true)) { std::cout << "FAIL: p.py" << std::endl; ++fails; }
  if (!(M::g(1) == true)) { std::cout << "FAIL: M::g(1)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All nested_binder_scope_check tests passed!" << std::endl;
  return fails;
}
