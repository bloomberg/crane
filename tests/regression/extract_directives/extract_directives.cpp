#include "extract_directives.h"

uint64_t ExtractDirectives::offset(uint64_t base, uint64_t x) {
  return (x + base);
}

uint64_t ExtractDirectives::scale(uint64_t base, uint64_t x) {
  return (x * base);
}

uint64_t ExtractDirectives::transform(uint64_t base, uint64_t x) {
  return scale(base, offset(base, x));
}

uint64_t ExtractDirectives::safe_pred(uint64_t n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    uint64_t n0 = n - 1;
    return n0;
  }
}

uint64_t ExtractDirectives::inner_add(uint64_t x0_, uint64_t x1_) {
  return (x0_ + x1_);
}

uint64_t ExtractDirectives::inner_mul(uint64_t x0_, uint64_t x1_) {
  return (x0_ * x1_);
}

uint64_t ExtractDirectives::outer_use(uint64_t a, uint64_t b) {
  return (inner_add(a, b) + inner_mul(a, b));
}
