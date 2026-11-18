// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <branch_callables_distinct_types.h>

#include <cstdint>
#include <iostream>

#define M BranchCallablesDistinctTypes

int main() {
  int fails = 0;
  if (!(M::t == 4)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::u == 11)) { std::cout << "FAIL: M::u" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All branch_callables_distinct_types tests passed!" << std::endl;
  return fails;
}
