#include "type_args_extraction.h"

uint64_t double_n(uint64_t n) {
  return [&]() -> uint64_t {
    static std::function<uint64_t(uint64_t)> __self;
    __self = [](uint64_t n0) {
      if (n0 <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t x = n0 - 1;
        uint64_t x_ = __self(x);
        return (UINT64_C(2) + x_);
      }
    };
    return __self(n);
    ;
  }();
}
