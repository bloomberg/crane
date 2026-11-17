#include "deep_tail_recursion_overflow.h"

DeepTailRecursionOverflow::chain
DeepTailRecursionOverflow::build(uint64_t n,
                                 DeepTailRecursionOverflow::chain acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  DeepTailRecursionOverflow::chain _loop_acc = std::move(acc);
  uint64_t _loop_n = n;
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

uint64_t
DeepTailRecursionOverflow::total_of(const DeepTailRecursionOverflow::chain &c) {
  // Explicit stack replaces the non-tail recursion of total_of: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    const DeepTailRecursionOverflow::chain *c;
  };

  struct _after_total_of_in_Link {
    uint64_t a1;
  };

  using _frame = std::variant<_call, _after_total_of_in_Link>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&c});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const DeepTailRecursionOverflow::chain &c = *_f.c;
      if (std::holds_alternative<
              typename DeepTailRecursionOverflow::chain::End_>(c.v())) {
        const auto &[a0] =
            std::get<typename DeepTailRecursionOverflow::chain::End_>(c.v());
        _result = std::move(a0);
      } else {
        const auto &[a0, a1] =
            std::get<typename DeepTailRecursionOverflow::chain::Link>(c.v());
        _stack.emplace_back(_after_total_of_in_Link{a1});
        _stack.emplace_back(_call{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<_after_total_of_in_Link>(_popped));
      _stack.pop_back();
      uint64_t a1 = _f.a1;
      _result = (a1 + std::move(_result));
    }
  }
  return _result;
}
