#include "sigma_assertion_after_implicit.h"

uint64_t SigmaAssertionAfterImplicit::f(
    const Sig<uint64_t> &x,
    const Sig<uint64_t> &y) { // Precondition: (S n <= 3)
  // Precondition: x.x >= 6
  assert(x.x >= 6);
  return ([&]() {
    const auto &[x0] = x;
    return x0;
  }() +
          [&]() {
            const auto &[x0] = y;
            return x0;
          }());
}
