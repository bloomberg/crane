// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <self_comparison_werror.h>

#include <cstdint>
#include <iostream>

#define M SelfComparisonWerror

int main() {
  int fails = 0;
  if (!(M::le_self(4) == true)) { std::cout << "FAIL: M::le_self(4)" << std::endl; ++fails; }
  if (!(M::eq_self(4) == true)) { std::cout << "FAIL: M::eq_self(4)" << std::endl; ++fails; }
  if (!(M::lt_self(4) == false)) { std::cout << "FAIL: M::lt_self(4)" << std::endl; ++fails; }
  if (!(M::bool_eq_self(false) == true)) { std::cout << "FAIL: M::bool_eq_self(false)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All self_comparison_werror tests passed!" << std::endl;
  return fails;
}
