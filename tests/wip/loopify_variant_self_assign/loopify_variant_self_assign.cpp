#include "loopify_variant_self_assign.h"

/// KNOWN BUG: self-assignment of a loop variable from its own sub-field.
///
/// drain is tail recursive. One branch passes a freshly built list, so the
/// loop variable for l has to be an owning value rather than a pointer; the
/// other branch passes the scrutinee's own tail, which loopification emits as
/// a direct self-assignment:
///
/// const auto &a0, a1 = std::get<Cons>(_loop_l.v());
/// _loop_s  = _loop_s + a0;
/// _loop_l  = *a1;        // source is owned by _loop_l itself
///
/// _loop_l is the sole owner of the cell a1 points at, so the assignment
/// destroys its own source. When the source cell uses a *different*
/// constructor than the destination (One vs Cons), std::variant's
/// assignment path is destroy-then-construct: it runs ~Cons, which drops
/// the last shared_ptr to the One cell, and then copy-constructs One out
/// of the freed cell.
///
/// A three-constructor inductive is what makes this visible: with only two
/// constructors the surviving alternative is the empty Nil, so nothing is
/// read back out of the freed storage.
///
/// Expected: go 8 = 20, go 12 = 42 (checked with Compute in Rocq).
/// Actual:   both return 2, plus an ASan heap-use-after-free.
///
/// Without Set Crane Loopify the same file extracts to correct code.
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
        _loop_l = *a1;
        _loop_n = m;
      }
    }
  }
}

uint64_t LoopifyVariantSelfAssign::go(uint64_t n) {
  return drain(n, lst::one(UINT64_C(1)), UINT64_C(0));
}
