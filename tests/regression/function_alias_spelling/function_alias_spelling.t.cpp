// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <function_alias_spelling.h>

#include <cstdint>
#include <iostream>

#define M FunctionAliasSpelling

int main() {
  int fails = 0;
  if (!(M::t1_leaf)) { std::cout << "FAIL: M::t1_leaf" << std::endl; ++fails; }
  if (!(M::z1 == 5)) { std::cout << "FAIL: M::z1" << std::endl; ++fails; }
  if (!(M::z2 == 0)) { std::cout << "FAIL: M::z2" << std::endl; ++fails; }
  if (!(M::b2)) { std::cout << "FAIL: M::b2" << std::endl; ++fails; }
  if (!(M::n2 == 4)) { std::cout << "FAIL: M::n2" << std::endl; ++fails; }
  if (!(M::f3.has_value() && *M::f3)) { std::cout << "FAIL: M::f3" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All function_alias_spelling tests passed!" << std::endl;
  return fails;
}
