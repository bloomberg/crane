// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <pos_add_loopify_reuse_shared.h>

#include <cstdint>
#include <iostream>

#define M PosAddLoopifyReuseShared

int main() {
  int fails = 0;
  if (!(M::a == 28)) { std::cout << "FAIL: M::a" << std::endl; ++fails; }
  if (!(M::b == 28)) { std::cout << "FAIL: M::b" << std::endl; ++fails; }
  if (!(M::c == 2)) { std::cout << "FAIL: M::c" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All pos_add_loopify_reuse_shared tests passed!" << std::endl;
  return fails;
}
