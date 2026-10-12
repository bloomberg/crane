#include "prop_binder_before_type_binder.h"

bool Nat::eq_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      uint64_t _x = m - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      bool s = eq_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}
