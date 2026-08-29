#include "loopify_computed_scrutinee_temp.h"

uint64_t
LoopifyComputedScrutineeTemp::hd(const LoopifyComputedScrutineeTemp::lst &l) {
  if (std::holds_alternative<typename LoopifyComputedScrutineeTemp::lst::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename LoopifyComputedScrutineeTemp::lst::Cons>(l.v());
    return a0;
  }
}

LoopifyComputedScrutineeTemp::lst
LoopifyComputedScrutineeTemp::wrap(uint64_t m,
                                   LoopifyComputedScrutineeTemp::lst l) {
  return lst::cons(UINT64_C(7), lst::cons(m, std::move(l)));
}

uint64_t LoopifyComputedScrutineeTemp::walk(
    uint64_t n,
    const LoopifyComputedScrutineeTemp::lst
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    LoopifyComputedScrutineeTemp::lst l;
    uint64_t n;
  };

  /// _Resume_Cons: saves [_s0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t _s0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, n});
  /// Loopified walk: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyComputedScrutineeTemp::lst &l = std::move(_f.l);
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = UINT64_C(0);
      } else {
        uint64_t m = n - 1;
        auto &&_sv = wrap(m, l);
        if (std::holds_alternative<
                typename LoopifyComputedScrutineeTemp::lst::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] =
              std::get<typename LoopifyComputedScrutineeTemp::lst::Cons>(
                  _sv.v());
          _stack.emplace_back(_Resume_Cons{(a0 + hd(l))});
          _stack.emplace_back(_Enter{*a1, m});
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f._s0 + std::move(_result));
    }
  }
  return _result;
}

uint64_t LoopifyComputedScrutineeTemp::go(uint64_t n) {
  return walk(n, lst::nil());
}
