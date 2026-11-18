// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <unused_let_local_fix_werror.h>

#include <cstdint>
#include <iostream>

#define M UnusedLetLocalFixWerror

int main() {
  int fails = 0;
  if (!(M::f(1) == 0)) { std::cout << "FAIL: M::f(1)" << std::endl; ++fails; }
  if (!(M::g(1) == 3)) { std::cout << "FAIL: M::g(1)" << std::endl; ++fails; }
  if (!(M::h(1) == 4)) { std::cout << "FAIL: M::h(1)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All unused_let_local_fix_werror tests passed!" << std::endl;
  return fails;
}
