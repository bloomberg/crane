// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <poly_nil_pair_type_erased.h>

#include <cstdint>
#include <iostream>

#define M PolyNilPairTypeErased

int main() {
  int fails = 0;
  if (!(M::t == 3)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All poly_nil_pair_type_erased tests passed!" << std::endl;
  return fails;
}
