#include "deep_tail_recursion_overflow.h"

DeepTailRecursionOverflow::chain
DeepTailRecursionOverflow::build(uint64_t n,
                                 DeepTailRecursionOverflow::chain acc) {
  DeepTailRecursionOverflow::chain _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t k = _loop_n - 1;
      uint64_t _next_n = k;
      _loop_acc = chain::link(std::move(_loop_acc), _loop_n);
      _loop_n = _next_n;
    }
  }
}

uint64_t DeepTailRecursionOverflow::total_of(
    const DeepTailRecursionOverflow::chain
        &c) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const DeepTailRecursionOverflow::chain *c;
  };

  /// _Resume_Link: saves [a1], resumes after recursive call with _result.
  struct _Resume_Link {
    uint64_t a1;
  };

  using _Frame = std::variant<_Enter, _Resume_Link>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{&c});
  /// Loopified total_of: _Enter -> _Resume_Link.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const DeepTailRecursionOverflow::chain &c = *_f.c;
      if (std::holds_alternative<
              typename DeepTailRecursionOverflow::chain::End_>(c.v())) {
        const auto &[a0] =
            std::get<typename DeepTailRecursionOverflow::chain::End_>(c.v());
        _result = std::move(a0);
      } else {
        const auto &[a0, a1] =
            std::get<typename DeepTailRecursionOverflow::chain::Link>(c.v());
        _stack.emplace_back(_Resume_Link{a1});
        _stack.emplace_back(_Enter{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Link>(_frame));
      _result = (_f.a1 + std::move(_result));
    }
  }
  return _result;
}
