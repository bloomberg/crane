#include "loopify_tmc.h"

/// Tests for Tail Modulo Cons (TMC) loopification optimization.
/// Functions where the recursive call is wrapped in a single constructor
/// should be optimized to use O(1) extra space via destination-passing style.
/// range lo hi creates lo, lo+1, ..., hi-1.
LoopifyTmc::list<uint64_t>
LoopifyTmc::range(uint64_t lo,
                  uint64_t hi) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

  struct _Enter {
    uint64_t hi;
  };

  /// _Resume1: saves [hi_], resumes after recursive call with _result.
  struct _Resume1 {
    uint64_t hi_;
  };

  using _Frame = std::variant<_Enter, _Resume1>;
  LoopifyTmc::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{hi});
  /// Loopified range: _Enter -> _Resume1.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t hi = _f.hi;
      if (hi <= 0) {
        _result = list<uint64_t>::nil();
      } else {
        uint64_t hi_ = hi - 1;
        if (lo <= hi_) {
          _stack.emplace_back(_Resume1{hi_});
          _stack.emplace_back(_Enter{hi_});
        } else {
          _result = list<uint64_t>::nil();
        }
      }
    } else {
      auto _f = std::move(std::get<_Resume1>(_frame));
      _result = list<uint64_t>::cons(_f.hi_, _result);
    }
  }
  return _result;
}

/// prefix_sums acc l computes running prefix sums.
LoopifyTmc::list<uint64_t> LoopifyTmc::prefix_sums(
    uint64_t acc,
    const LoopifyTmc::list<uint64_t>
        &l) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    const LoopifyTmc::list<uint64_t> *l;
    uint64_t acc;
  };

  /// _Resume_Cons: saves [s], resumes after recursive call with _result.
  struct _Resume_Cons {
    uint64_t s;
  };

  using _Frame = std::variant<_Enter, _Resume_Cons>;
  LoopifyTmc::list<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{&l, acc});
  /// Loopified prefix_sums: _Enter -> _Resume_Cons.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const LoopifyTmc::list<uint64_t> &l = *_f.l;
      uint64_t acc = _f.acc;
      if (std::holds_alternative<typename LoopifyTmc::list<uint64_t>::Nil>(
              l.v())) {
        _result = list<uint64_t>::nil();
      } else {
        const auto &[a0, a1] =
            std::get<typename LoopifyTmc::list<uint64_t>::Cons>(l.v());
        uint64_t s = (acc + a0);
        _stack.emplace_back(_Resume_Cons{s});
        _stack.emplace_back(_Enter{a1.get(), s});
      }
    } else {
      auto _f = std::move(std::get<_Resume_Cons>(_frame));
      _result = list<uint64_t>::cons(_f.s, _result);
    }
  }
  return _result;
}
