#include "tyarg_family_binder_shift.h"

uint64_t TyargFamilyBinderShift::count_down(uint64_t x) {
  if (x <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t k = x - 1;
    return (count_down(k) + 1);
  }
}
