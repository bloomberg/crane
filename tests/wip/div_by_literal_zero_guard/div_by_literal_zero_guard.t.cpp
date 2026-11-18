// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <div_by_literal_zero_guard.h>

#include <cstdint>
#include <iostream>

#define M DivByLiteralZeroGuard

int main() {
  int fails = 0;
  if (!(M::t == 5)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All div_by_literal_zero_guard tests passed!" << std::endl;
  return fails;
}
