#include "deep_tail_recursion_overflow.h"

DeepTailRecursionOverflow::chain
DeepTailRecursionOverflow::build(uint64_t n,
                                 DeepTailRecursionOverflow::chain acc) {
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

uint64_t DeepTailRecursionOverflow::total_of(
    const DeepTailRecursionOverflow::chain
        &c) { /// CraneEnter: captures varying parameters for each recursive
              /// call.

  struct CraneEnter {
    const DeepTailRecursionOverflow::chain *c;
  };

  /// CraneCont_Link: saves [a1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_Link {
    uint64_t a1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_Link>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{&c});
  /// Loopified total_of: CraneEnter -> CraneCont_Link.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const DeepTailRecursionOverflow::chain &c = *_f.c;
      if (std::holds_alternative<
              typename DeepTailRecursionOverflow::chain::End_>(c.v())) {
        const auto &[a0] =
            std::get<typename DeepTailRecursionOverflow::chain::End_>(c.v());
        _result = std::move(a0);
      } else {
        const auto &[a0, a1] =
            std::get<typename DeepTailRecursionOverflow::chain::Link>(c.v());
        _stack.emplace_back(CraneCont_Link{a1});
        _stack.emplace_back(CraneEnter{crane_raw(a0)});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Link>(_frame));
      uint64_t a1 = _f.a1;
      _result = (a1 + std::move(_result));
    }
  }
  return _result;
}
