// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <branch_pair_fn_param_convention.h>

#include <cstdint>
#include <iostream>

#define M BranchPairFnParamConvention

int main() {
  int fails = 0;
  if (!(M::t(true) == 1)) { std::cout << "FAIL: M::t(true)" << std::endl; ++fails; }
  if (!(M::t(false) == 2)) { std::cout << "FAIL: M::t(false)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All branch_pair_fn_param_convention tests passed!" << std::endl;
  return fails;
}
