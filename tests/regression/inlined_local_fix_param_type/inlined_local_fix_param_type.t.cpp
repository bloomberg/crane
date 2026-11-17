// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <inlined_local_fix_param_type.h>

#include <cstdint>
#include <iostream>

#define M InlinedLocalFixParamType

int main() {
  int fails = 0;
  if (!(M::t == 0)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::u == 2)) { std::cout << "FAIL: M::u" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All inlined_local_fix_param_type tests passed!" << std::endl;
  return fails;
}
