// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <rocq_string_type_undeclared.h>

#include <cstdint>
#include <iostream>

#define M RocqStringTypeUndeclared

int main() {
  int fails = 0;
  if (!(M::t == 7)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All rocq_string_type_undeclared tests passed!" << std::endl;
  return fails;
}
