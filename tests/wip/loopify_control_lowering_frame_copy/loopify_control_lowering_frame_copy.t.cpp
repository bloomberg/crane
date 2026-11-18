// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_control_lowering_frame_copy.h>

#include <cstdint>
#include <iostream>

#define M LoopifyControlLoweringFrameCopy

int main() {
  int fails = 0;
  auto l = List<List<bool>>::cons(List<bool>::nil(), List<List<bool>>::nil());
  if (!(M::g3(l, 1, 2).second == true)) { std::cout << "FAIL: M::g3(l, 1, 2).second" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_control_lowering_frame_copy tests passed!" << std::endl;
  return fails;
}
