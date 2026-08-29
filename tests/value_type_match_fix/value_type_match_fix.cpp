#include "value_type_match_fix.h"

std::optional<std::function<uint64_t(uint64_t)>>
ValueTypeMatchFix::make_adder_from_triple(const ValueTypeMatchFix::triple &t) {
  const auto &[a0, a1, a2] = t;
  uint64_t base = ((a0 + a1) + a2);
  auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return base;
    } else {
      uint64_t x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go = [=](uint64_t x) mutable -> uint64_t { return go_impl(go_impl, x); };
  return std::make_optional<std::function<uint64_t(uint64_t)>>(go);
}

std::optional<std::function<uint64_t(uint64_t)>>
ValueTypeMatchFix::make_field_adder(const ValueTypeMatchFix::triple &t) {
  const auto &[a0, a1, a2] = t;
  auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
    if (x <= 0) {
      return a0;
    } else {
      uint64_t x_ = x - 1;
      return (_self_go(_self_go, x_) + 1);
    }
  };
  auto go = [=](uint64_t x) mutable -> uint64_t { return go_impl(go_impl, x); };
  return std::make_optional<std::function<uint64_t(uint64_t)>>(go);
}
