// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_reread_loop_pointer.h>

#include <cstdint>
#include <iostream>

#define M LoopifyRereadLoopPointer

int main() {
  int fails = 0;
  auto tr = M::tree::node(M::tree::leaf(), 1, M::tree::leaf());
  if (!(M::g(tr) == true)) { std::cout << "FAIL: M::g(tr)" << std::endl; ++fails; }
  if (!(M::g(M::tree::leaf()) == true)) { std::cout << "FAIL: M::g(Leaf)" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_reread_loop_pointer tests passed!" << std::endl;
  return fails;
}
