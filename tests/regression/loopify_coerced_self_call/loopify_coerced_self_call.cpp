#include "loopify_coerced_self_call.h"

Nat::EvenT Nat::EvenT_2(uint64_t, uint64_t h0) {
  // Precondition: n == (2 * m)
  const uint64_t &x = h0;
  return (x + 1);
}

Nat::EvenT Nat::even_EvenT(uint64_t n) {
  // Explicit stack replaces the non-tail recursion of even_EvenT: _call frames
  // are pending calls, _after frames resume a caller.
  struct _call {
    uint64_t n;
  };

  struct _after_even_EvenT_in_S {
    uint64_t n1;
  };

  using _frame = std::variant<_call, _after_even_EvenT_in_S>;
  Nat::EvenT _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{n});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = EvenT_0;
      } else {
        uint64_t n0 = n - 1;
        if (n0 <= 0) {
          throw std::logic_error("absurd case");
        } else {
          uint64_t n1 = n0 - 1;
          _stack.emplace_back(_after_even_EvenT_in_S{n1});
          _stack.emplace_back(_call{n1});
        }
      }
    } else {
      auto _f = std::move(std::get<_after_even_EvenT_in_S>(_popped));
      _stack.pop_back();
      uint64_t n1 = _f.n1;
      Nat::EvenT he = std::move(_result);
      _result = EvenT_2(n1, std::move(he));
    }
  }
  return _result;
}

/// A recursive call made through a coercion of its callee is a recursive
/// call.
///
/// Nat.even_EvenT calls itself as (magic even_EvenT) n', the coercion
/// standing for the change of index in its result type, and the C++ calls
/// even_EvenT(n1) where it stands, below the frame that binds the result.
/// The recursion plan read only a callee written as a bare global, saw no
/// recursion, and the function was left calling itself: half of two
/// million ran two million C++ frames deep.
uint64_t LoopifyCoercedSelfCall::half(uint64_t n) { return Nat::even_EvenT(n); }
