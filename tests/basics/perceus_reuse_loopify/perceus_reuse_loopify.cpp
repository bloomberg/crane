#include "perceus_reuse_loopify.h"

R::lst R::rev_append1(const R::lst &l, R::lst acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
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

uint64_t R::sum1(const R::lst &l) {
  // Explicit stack replaces the non-tail recursion of sum1: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const R::lst *l;
  };

  struct _after_sum1_in_Cons {
    uint64_t a0;
  };

  using _frame = std::variant<_call, _after_sum1_in_Cons>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&l});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const R::lst &l = *_f.l;
      if (std::holds_alternative<typename R::lst::Nil>(l.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename R::lst::Cons>(l.v());
        _stack.emplace_back(_after_sum1_in_Cons{a0});
        _stack.emplace_back(_call{crane_raw(a1)});
      }
    } else {
      auto _f = std::move(std::get<_after_sum1_in_Cons>(_popped));
      _stack.pop_back();
      uint64_t a0 = _f.a0;
      _result = (a0 + _result);
    }
  }
  return _result;
}
