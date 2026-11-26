#include "eq_dec_self_werror.h"

uint64_t EqDecSelfWerror::f(uint64_t x) {
  if (x == x) {
    return UINT64_C(1);
  } else {
    return UINT64_C(2);
  }
}
