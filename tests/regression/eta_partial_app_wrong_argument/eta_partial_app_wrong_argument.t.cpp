// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <eta_partial_app_wrong_argument.h>

#include <cstdint>
#include <iostream>

#define M EtaPartialAppWrongArgument

int main() {
  int fails = 0;
  if (!(M::t == false)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All eta_partial_app_wrong_argument tests passed!" << std::endl;
  return fails;
}
