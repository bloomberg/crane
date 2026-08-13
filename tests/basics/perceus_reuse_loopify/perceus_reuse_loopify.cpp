#include "perceus_reuse_loopify.h"

R::lst R::rev_append1(const R::lst &l, R::lst acc) {
  R::lst _loop_acc = std::move(acc);
  const R::lst *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename R::lst::Nil>(_loop_l->v())) {
      return _loop_acc;
    } else {
      const auto &[a0, a1] = std::get<typename R::lst::Cons>(_loop_l->v());
      _loop_acc = lst::cons(a0, std::move(_loop_acc));
      _loop_l = crane_raw(a1);
    }
  }
}

R::lst R::rev1(const R::lst &l) { return rev_append1(l, lst::nil()); }

uint64_t R::sum1(const R::lst &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

  struct _Enter {
    const R::lst *l;
  };

  /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t a0;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  uint64_t _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l});
  /// Loopified sum1: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const R::lst &l = *_f.l;
      if (std::holds_alternative<typename R::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename R::lst::Cons>(l.v());
        _stack.emplace_back(_Resume_Cons{a0});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = (_f.a0 + std::move(_result));
    }
  }
  return _result;
}
