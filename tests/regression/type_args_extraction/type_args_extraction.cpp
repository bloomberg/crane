#include "type_args_extraction.h"

uint64_t double_n(uint64_t n) {
  return crane::rec<uint64_t, uint64_t>(
      [](uint64_t n0) -> uint64_t {
        if (n0 <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t x = n0 - 1;
          uint64_t x_ = crane::rec_call<uint64_t, uint64_t>(x);
          return UINT64_C(2) + x_;
        }
      },
      n);
}
