// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <bool_negation_self_werror.h>

#include <cstdint>
#include <iostream>

#define M BoolNegationSelfWerror

int main() {
  int fails = 0;
  if (!(M::f(false) == true)) { std::cout << "FAIL: M::f(false)" << std::endl; ++fails; }
  if (!(M::g(true) == false)) { std::cout << "FAIL: M::g(true)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All bool_negation_self_werror tests passed!" << std::endl;
  return fails;
}
