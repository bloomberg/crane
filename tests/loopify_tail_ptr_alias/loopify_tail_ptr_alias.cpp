#include "loopify_tail_ptr_alias.h"

uint64_t LoopifyTailPtrAlias::hd(const LoopifyTailPtrAlias::lst &l) {
  if (std::holds_alternative<typename LoopifyTailPtrAlias::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyTailPtrAlias::lst::Cons>(l.v());
    return a0;
  }
}

uint64_t LoopifyTailPtrAlias::rot(uint64_t n, const LoopifyTailPtrAlias::lst &l,
                                  const LoopifyTailPtrAlias::lst &acc,
                                  uint64_t s) {
  uint64_t _loop_s = std::move(s);
  LoopifyTailPtrAlias::lst _loop_acc = acc;
  LoopifyTailPtrAlias::lst _loop_l = l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_s;
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename LoopifyTailPtrAlias::lst::Nil>(
              _loop_l.v())) {
        return _loop_s;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyTailPtrAlias::lst::Cons>(_loop_l.v());
        if (a0 <= 0) {
          LoopifyTailPtrAlias::lst _next_acc = LoopifyTailPtrAlias::lst(*a1);
          _loop_s = (_loop_s + hd(_loop_acc));
          _loop_l = lst::cons(UINT64_C(0), lst::cons(m, lst::nil()));
          _loop_n = m;
          _loop_acc = std::move(_next_acc);
        } else {
          uint64_t _x = a0 - 1;
          return _loop_s;
        }
      }
    }
  }
}

uint64_t LoopifyTailPtrAlias::go(uint64_t n) {
  return rot(n, lst::cons(UINT64_C(0), lst::cons(UINT64_C(7), lst::nil())),
             lst::nil(), UINT64_C(0));
}
