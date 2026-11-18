// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <local_fix_nontail_function_result.h>

#include <cstdint>
#include <iostream>

#define M LocalFixNontailFunctionResult

int main() {
  int fails = 0;
  if (!(M::t == true)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::t2 == 1)) { std::cout << "FAIL: M::t2" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_nontail_function_result tests passed!" << std::endl;
  return fails;
}
