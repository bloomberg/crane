// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_local_fix_outer_call.h>

#include <cstdint>
#include <iostream>

#define M LoopifyLocalFixOuterCall

int main() {
  int fails = 0;
  auto l = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  auto r = M::g(l);
  auto want = List<uint64_t>::cons(2, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  if (!(r.length() == 2)) { std::cout << "FAIL: r.length()" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_local_fix_outer_call tests passed!" << std::endl;
  return fails;
}
