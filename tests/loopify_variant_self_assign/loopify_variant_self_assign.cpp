#include "loopify_variant_self_assign.h"

uint64_t LoopifyVariantSelfAssign::drain(uint64_t n,
                                         const LoopifyVariantSelfAssign::lst &l,
                                         uint64_t s) {
  uint64_t _loop_s = std::move(s);
  LoopifyVariantSelfAssign::lst _loop_l = l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_s;
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename LoopifyVariantSelfAssign::lst::Nil>(
              _loop_l.v())) {
        return _loop_s;
      } else if (std::holds_alternative<
                     typename LoopifyVariantSelfAssign::lst::One>(
                     _loop_l.v())) {
        const auto &[a0] =
            std::get<typename LoopifyVariantSelfAssign::lst::One>(_loop_l.v());
        _loop_s = (_loop_s + a0);
        _loop_l = lst::cons(a0, lst::one((a0 + UINT64_C(1))));
        _loop_n = m;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyVariantSelfAssign::lst::Cons>(_loop_l.v());
        _loop_s = (_loop_s + a0);
        _loop_l = LoopifyVariantSelfAssign::lst(*a1);
        _loop_n = m;
      }
    }
  }
}

uint64_t LoopifyVariantSelfAssign::go(uint64_t n) {
  return drain(n, lst::one(UINT64_C(1)), UINT64_C(0));
}
