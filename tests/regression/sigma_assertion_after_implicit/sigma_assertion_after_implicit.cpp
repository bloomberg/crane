#include "sigma_assertion_after_implicit.h"

uint64_t SigmaAssertionAfterImplicit::f(uint64_t x, uint64_t y) {
  // Precondition: (S n <= 3)
  // Precondition: x >= 6
  assert(x >= 6);
  return x + y;
}
