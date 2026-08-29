#include "fix_escape_capture.h"

std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
FixEscapeCapture::make_pair_fn(uint64_t base) {
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
  return std::make_pair(std::move(base), add);
}

std::pair<uint64_t, std::function<uint64_t(uint64_t)>>
FixEscapeCapture::make_pair_fn2(uint64_t base) {
  auto id_add_impl = [=](auto &_self_id_add, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (_self_id_add(_self_id_add, x_) + 1);
    }
  };
  auto id_add = [=](uint64_t x) mutable -> uint64_t {
    return id_add_impl(id_add_impl, x);
  };
  return std::make_pair(id_add(base), id_add);
}
