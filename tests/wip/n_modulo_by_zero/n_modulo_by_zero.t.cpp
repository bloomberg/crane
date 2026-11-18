// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <n_modulo_by_zero.h>

#include <cstdint>
#include <iostream>

#define M NModuloByZero

int main() {
  int fails = 0;
  if (!(M::a(4, 0) == 4)) { std::cout << "FAIL: M::a(4, 0)" << std::endl; ++fails; }
  if (!(M::t == 4)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::a(7, 3) == 1)) { std::cout << "FAIL: M::a(7, 3)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All n_modulo_by_zero tests passed!" << std::endl;
  return fails;
}
