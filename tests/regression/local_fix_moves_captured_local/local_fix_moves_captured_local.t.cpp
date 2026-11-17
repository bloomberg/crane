// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <local_fix_moves_captured_local.h>

#include <cstdint>
#include <iostream>

#define M LocalFixMovesCapturedLocal

int main() {
  int fails = 0;
  if (!(M::t == 1)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All local_fix_moves_captured_local tests passed!" << std::endl;
  return fails;
}
