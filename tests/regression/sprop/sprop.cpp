#include "sprop.h"

uint64_t SPropTest::guarded_pred(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m = n - 1;
    return m;
  }
}

uint64_t SPropTest::safe_div(uint64_t _x0, uint64_t _x1) {
  return (_x1 ? _x0 / _x1 : 0);
}
