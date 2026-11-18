// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <cofix_unused_param_as_value.h>

#include <cstdint>
#include <iostream>

#define M CofixUnusedParamAsValue

int main() {
  int fails = 0;
  if (!(M::t == 2)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All cofix_unused_param_as_value tests passed!" << std::endl;
  return fails;
}
