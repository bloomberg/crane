// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <lifted_local_fix_drops_capture.h>

#include <cstdint>
#include <iostream>

#define M LiftedLocalFixDropsCapture

int main() {
  int fails = 0;
  if (!(M::t == 7)) { std::cout << "FAIL: M::t" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All lifted_local_fix_drops_capture tests passed!" << std::endl;
  return fails;
}
