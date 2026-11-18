// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <methodified_constraint_tparam.h>

#include <cstdint>
#include <iostream>

#define M MethodifiedConstraintTparam

int main() {
  int fails = 0;
  if (!(M::t == 4)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All methodified_constraint_tparam tests passed!" << std::endl;
  return fails;
}
