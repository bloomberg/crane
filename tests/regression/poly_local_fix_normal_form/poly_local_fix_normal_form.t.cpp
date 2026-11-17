// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <poly_local_fix_normal_form.h>

#include <cstdint>
#include <iostream>

#define M PolyLocalFixNormalForm

int main() {
  int fails = 0;
  if (!(M::t == 1)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All poly_local_fix_normal_form tests passed!" << std::endl;
  return fails;
}
