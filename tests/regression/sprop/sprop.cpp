#include "sprop.h"

uint64_t SPropTest::guarded_pred(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    return m;
  }
}

uint64_t SPropTest::safe_div(uint64_t x0_, uint64_t x1_) {
  return (x1_ ? x0_ / x1_ : 0);
}
