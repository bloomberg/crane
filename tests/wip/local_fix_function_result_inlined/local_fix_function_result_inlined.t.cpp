// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <local_fix_function_result_inlined.h>

#include <cstdint>
#include <iostream>

#define M LocalFixFunctionResultInlined

int main() {
  int fails = 0;
  if (!(M::t == 1)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::u == false)) { std::cout << "FAIL: M::u" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_function_result_inlined tests passed!" << std::endl;
  return fails;
}
