#include "loopify_mutual_inline_temp.h"

LoopifyMutualInlineTemp::lst
LoopifyMutualInlineTemp::build(uint64_t n, LoopifyMutualInlineTemp::lst acc) {
  LoopifyMutualInlineTemp::lst _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t _next_n = m;
      _loop_acc = lst::cons(_loop_n, std::move(_loop_acc));
      _loop_n = _next_n;
    }
  }
}

uint64_t LoopifyMutualInlineTemp::hd(const LoopifyMutualInlineTemp::lst &l) {
  if (std::holds_alternative<typename LoopifyMutualInlineTemp::lst::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyMutualInlineTemp::lst::Cons>(l.v());
    return a0;
  }
}

uint64_t LoopifyMutualInlineTemp::even_step(
    uint64_t n, const LoopifyMutualInlineTemp::lst &l,
    const LoopifyMutualInlineTemp::lst &keep, uint64_t s) {
  uint64_t _loop_s = std::move(s);
  LoopifyMutualInlineTemp::lst _loop_keep = keep;
  LoopifyMutualInlineTemp::lst _loop_l = l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return (_loop_s + hd(_loop_keep));
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename LoopifyMutualInlineTemp::lst::Nil>(
              _loop_l.v())) {
        return _loop_s;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyMutualInlineTemp::lst::Cons>(_loop_l.v());
        uint64_t _inl_s = (_loop_s + a0);
        const LoopifyMutualInlineTemp::lst &_inl_keep = *a1;
        const LoopifyMutualInlineTemp::lst &_inl_l =
            lst::cons(a0, lst::cons(a0, lst::nil()));
        uint64_t _inl_n = m;
        if (_inl_n <= 0) {
          return (_inl_s + hd(_inl_keep));
        } else {
          uint64_t m = _inl_n - 1;
          if (std::holds_alternative<
                  typename LoopifyMutualInlineTemp::lst::Nil>(_inl_l.v())) {
            return _inl_s;
          } else {
            const auto &[a0, a1] =
                std::get<typename LoopifyMutualInlineTemp::lst::Cons>(
                    _inl_l.v());
            _loop_s = (_inl_s + hd(_inl_keep));
            _loop_keep = LoopifyMutualInlineTemp::lst(*a1);
            _loop_l = lst::cons((a0 + UINT64_C(1)), lst::nil());
            _loop_n = m;
          }
        }
      }
    }
  }
}

uint64_t LoopifyMutualInlineTemp::odd_step(
    uint64_t n, const LoopifyMutualInlineTemp::lst &l,
    const LoopifyMutualInlineTemp::lst &keep, uint64_t s) {
  uint64_t _loop_s = std::move(s);
  LoopifyMutualInlineTemp::lst _loop_keep = keep;
  LoopifyMutualInlineTemp::lst _loop_l = l;
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return (_loop_s + hd(_loop_keep));
    } else {
      uint64_t m = _loop_n - 1;
      if (std::holds_alternative<typename LoopifyMutualInlineTemp::lst::Nil>(
              _loop_l.v())) {
        return _loop_s;
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyMutualInlineTemp::lst::Cons>(_loop_l.v());
        uint64_t _inl_s = (_loop_s + hd(_loop_keep));
        const LoopifyMutualInlineTemp::lst &_inl_keep = *a1;
        const LoopifyMutualInlineTemp::lst &_inl_l =
            lst::cons((a0 + UINT64_C(1)), lst::nil());
        uint64_t _inl_n = m;
        if (_inl_n <= 0) {
          return (_inl_s + hd(_inl_keep));
        } else {
          uint64_t m = _inl_n - 1;
          if (std::holds_alternative<
                  typename LoopifyMutualInlineTemp::lst::Nil>(_inl_l.v())) {
            return _inl_s;
          } else {
            const auto &[a0, a1] =
                std::get<typename LoopifyMutualInlineTemp::lst::Cons>(
                    _inl_l.v());
            _loop_s = (_inl_s + a0);
            _loop_keep = LoopifyMutualInlineTemp::lst(*a1);
            _loop_l = lst::cons(a0, lst::cons(a0, lst::nil()));
            _loop_n = m;
          }
        }
      }
    }
  }
}

uint64_t LoopifyMutualInlineTemp::go(uint64_t n) {
  return even_step(n, build(UINT64_C(4), lst::nil()), lst::nil(), UINT64_C(0));
}
