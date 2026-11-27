#include "loopify_constant_local_fix.h"

uint64_t LoopifyConstantLocalFix::from_n(uint64_t n) {
  return [&]() {
    auto go = [&](const List<uint64_t> &l) -> List<uint64_t> {
      // Explicit stack replaces the non-tail recursion of go: _call frames are
      // pending calls, _after frames resume a caller.
      struct _call {
        const List<uint64_t> *l;
      };

      struct _after_go_in_Cons {
        uint64_t a0;
      };

      using _frame = std::variant<_call, _after_go_in_Cons>;
      List<uint64_t> _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{&l});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const List<uint64_t> &l = *_f.l;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
            _result = List<uint64_t>::nil();
          } else {
            const auto &[a0, a1] =
                std::get<typename List<uint64_t>::Cons>(l.v());
            _stack.emplace_back(_after_go_in_Cons{a0});
            _stack.emplace_back(_call{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_after_go_in_Cons>(_popped));
          _stack.pop_back();
          uint64_t a0 = _f.a0;
          _result = List<uint64_t>::cons(a0, std::move(_result));
        }
      }
      return _result;
    };
    return go(ListDef::template repeat<uint64_t>(UINT64_C(1), n));
  }().length();
}

uint64_t Nat::pow(uint64_t n, uint64_t m) {
  // Explicit stack replaces the non-tail recursion of pow: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    uint64_t m;
  };

  struct _after_pow_in_S {};

  using _frame = std::variant<_call, _after_pow_in_S>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{m});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t m = _f.m;
      if (m <= 0) {
        _result = UINT64_C(1);
      } else {
        uint64_t m0 = m - 1;
        _stack.emplace_back(_after_pow_in_S{});
        _stack.emplace_back(_call{m0});
      }
    } else {
      auto _f = std::move(std::get<_after_pow_in_S>(_popped));
      _stack.pop_back();
      _result = n * _result;
    }
  }
  return _result;
}
