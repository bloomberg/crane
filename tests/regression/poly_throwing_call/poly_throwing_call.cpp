#include "poly_throwing_call.h"

uint64_t PolyThrowingCall::count(uint64_t fuel, uint64_t n) {
  if (fuel <= 0) {
    return out_of_fuel<uint64_t>();
  } else {
    uint64_t f = fuel - 1;
    if (n == UINT64_C(0)) {
      return UINT64_C(0);
    } else {
      uint64_t r = count(f, (n - UINT64_C(1) > n ? 0 : n - UINT64_C(1)));
      return (r + 1);
    }
  }
}

bool PolyThrowingCall::flag(uint64_t fuel) {
  if (fuel <= 0) {
    return out_of_fuel<bool>();
  } else {
    uint64_t _x = fuel - 1;
    return true;
  }
}

uint64_t PolyThrowingCall::ok() { return count(UINT64_C(10), UINT64_C(3)); }

bool PolyThrowingCall::flag_ok() { return flag(UINT64_C(1)); }
