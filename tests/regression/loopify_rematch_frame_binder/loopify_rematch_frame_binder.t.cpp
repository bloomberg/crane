// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_rematch_frame_binder.h>

#include <cstdint>
#include <iostream>

#define M LoopifyRematchFrameBinder

int main() {
  int fails = 0;
  if (!std::holds_alternative<List<bool>::Nil>(M::h(3).v())) { std::cout << "FAIL: M::h(3) not nil" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_rematch_frame_binder tests passed!" << std::endl;
  return fails;
}
