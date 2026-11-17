// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <unused_pair_binding_redefinition.h>

#include <cstdint>
#include <iostream>

#define M UnusedPairBindingRedefinition

int main() {
  int fails = 0;
  if (!(M::f(3) == 5)) { std::cout << "FAIL: M::f(3)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All unused_pair_binding_redefinition tests passed!" << std::endl;
  return fails;
}
