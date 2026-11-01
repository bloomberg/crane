#include <loopify_partner_tail_and_invoked.h>
#include <cassert>
#include <cstdint>
#include <iostream>

using M = LoopifyPartnerTailAndInvoked;

// walk and step, each turn one iteration: walk (S m) adds 1 where m is odd
// and goes on in step m; step (S m) adds 1 and goes on in walk m.
static uint64_t reference(uint64_t n, bool walking) {
  uint64_t acc = 0;
  for (;;) {
    if (n == 0)
      return walking ? acc : acc + 1;
    uint64_t m = n - 1;
    if (!walking || m % 2 != 0)
      acc += 1;
    n = m;
    walking = !walking;
  }
}

int main() {
  for (uint64_t n = 0; n < 64; n++) {
    assert(M::walk(n) == reference(n, true));
    assert(M::step(n) == reference(n, false));
  }
  // Deep enough that one C++ frame per call between the two would overflow
  // the stack.
  uint64_t deep = M::walk(1000000);
  std::cout << "walk 1000000 = " << deep << " (want " << reference(1000000, true) << ")" << std::endl;
  assert(deep == reference(1000000, true));
  assert(M::step(1000001) == reference(1000001, false));
  return 0;
}
