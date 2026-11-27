#include "int63_arith.h"

int64_t Int63Arith::i_abs(int64_t x) {
  if (x < INT64_C(0)) {
    return static_cast<int64_t>((UINT64_C(0) - static_cast<uint64_t>(x)) &
                                UINT64_C(9223372036854775807));
  } else {
    return x;
  }
}
