// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <local_fix_alias_function_result.h>

#include <cstdint>
#include <iostream>

#define M LocalFixAliasFunctionResult

int main() {
  int fails = 0;
  if (!(M::t == 7)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_alias_function_result tests passed!" << std::endl;
  return fails;
}
