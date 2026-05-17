#include "fix_in_record.h"

FixInRecord::fn_box FixInRecord::make_box(uint64_t n) {
  uint64_t base = (n * UINT64_C(3));
  auto add_impl = [=](auto &_self_add, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (_self_add(_self_add, x_) + 1);
    }
  };
  auto add = [=](uint64_t x) mutable -> uint64_t {
    return add_impl(add_impl, x);
  };
  return fn_box{base, add};
}
