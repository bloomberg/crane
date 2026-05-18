#include "int63_arith.h"

int64_t Int63Arith::i_abs(int64_t x) {
  if (x < INT64_C(0)) {
    return ((INT64_C(0) - x) & 0x7FFFFFFFFFFFFFFFLL);
  } else {
    return x;
  }
}
