// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <poly_nil_type_erased.h>

#include <cstdint>
#include <iostream>

#define M PolyNilTypeErased

int main() {
  int fails = 0;
  if (!(M::t == 4)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }
  if (!(M::u == 2)) { std::cout << "FAIL: M::u" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All poly_nil_type_erased tests passed!" << std::endl;
  return fails;
}
