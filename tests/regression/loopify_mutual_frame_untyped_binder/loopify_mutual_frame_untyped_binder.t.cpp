// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_mutual_frame_untyped_binder.h>

#include <iostream>

#define M LoopifyMutualFrameUntypedBinder

int main() {
  int fails = 0;
  auto none = List<std::optional<uint64_t>>::nil();
  if (!(M::h1b(0, none) == 238)) { std::cout << "FAIL: M::h1b(0)" << std::endl; ++fails; }
  if (!(M::h1b(1, none) == 21)) { std::cout << "FAIL: M::h1b(1)" << std::endl; ++fails; }
  if (!(M::h1b(2, none) == 0)) { std::cout << "FAIL: M::h1b(2)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_mutual_frame_untyped_binder tests passed!" << std::endl;
  return fails;
}
