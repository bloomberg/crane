#include "stmonad.h"

uint64_t STMonadTests::fib_fun(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t m0 = n - 1;
    if (m0 <= 0) {
      return UINT64_C(1);
    } else {
      uint64_t m = m0 - 1;
      return (fib_fun(m0) + fib_fun(m));
    }
  }
}

uint64_t STMonadTests::double_n(uint64_t n) {
  return [&]() -> auto {
    static std::function<decltype(n)(uint64_t)> __self;
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

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
