#include "function_type_argument_curried.h"

uint64_t FunctionTypeArgumentCurried::f2(uint64_t x0_, uint64_t x1_) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto idp_1 =
      crane::immortal(idp<crane::fn<uint64_t(uint64_t, uint64_t)>>(
          [](uint64_t _x0, uint64_t _x1) -> uint64_t { return _x0 + _x1; }));
  return idp_1(x0_, x1_);
}

uint64_t
FunctionTypeArgumentCurried::ev(const FunctionTypeArgumentCurried::t &x) {
  const auto &[a0, a1, a2] = x;
  return a0 + a1 + a2;
}
