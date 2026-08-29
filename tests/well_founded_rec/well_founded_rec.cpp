#include "well_founded_rec.h"

List<uint64_t> WellFoundedRec::countdown_acc(uint64_t n) {
  if (n <= 0) {
    return List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil());
  } else {
    uint64_t m = n - 1;
    return List<uint64_t>::cons(n, countdown_acc(m));
  }
}

List<uint64_t> WellFoundedRec::countdown(uint64_t _x0) {
  return countdown_acc(_x0);
}

uint64_t WellFoundedRec::div2_wf(uint64_t x) {
  if (x <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n0 = x - 1;
    if (n0 <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t m = n0 - 1;
      return (div2_wf(m) + 1);
    }
  }
}

uint64_t WellFoundedRec::gcd_wf(uint64_t x, uint64_t b) {
  if (x <= 0) {
    return b;
  } else {
    uint64_t a_ = x - 1;
    uint64_t y = ((a_ + 1) ? b % (a_ + 1) : b);
    return gcd_wf(y, (a_ + 1));
  }
}
