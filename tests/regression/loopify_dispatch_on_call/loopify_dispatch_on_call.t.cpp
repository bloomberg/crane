#include <loopify_dispatch_on_call.h>

#include <cassert>
#include <cstdint>

using M = LoopifyDispatchOnCall;

static void check(uint64_t n, bool parity, uint64_t grafted_size, uint64_t twice_size, bool grafted_parity) {
  auto t = M::comb(n);
  auto g = M::graft(t);
  assert(M::parity(t) == parity);
  assert(M::size(g) == grafted_size);
  assert(M::size(M::graft(g)) == twice_size);
  assert(M::parity(g) == grafted_parity);
}

int main() {
  check(0, true, 1, 1, true);
  check(5, false, 20, 20, false);
  check(10, false, 232, 232, false);
  check(23, false, 121392, 121392, false);
  return 0;
}
