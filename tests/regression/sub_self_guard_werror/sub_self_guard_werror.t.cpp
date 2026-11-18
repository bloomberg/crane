// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <sub_self_guard_werror.h>

#include <cstdint>
#include <iostream>

#define M SubSelfGuardWerror

int main() {
  int fails = 0;
  if (!(M::f(3) == 0)) { std::cout << "FAIL: M::f(3)" << std::endl; ++fails; }
  if (!(M::g(3) == 0)) { std::cout << "FAIL: M::g(3)" << std::endl; ++fails; }
  if (!(M::h(3) == 1)) { std::cout << "FAIL: M::h(3)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All sub_self_guard_werror tests passed!" << std::endl;
  return fails;
}
