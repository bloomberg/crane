#include "int63_arith.h"

int64_t Int63Arith::i_abs(int64_t x) {
  if (x < INT64_C(0)) {
    return static_cast<int64_t>(
        (static_cast<uint64_t>(INT64_C(0)) - static_cast<uint64_t>(x)) &
        0x7FFFFFFFFFFFFFFFULL);
  } else {
    return x;
  }
}
