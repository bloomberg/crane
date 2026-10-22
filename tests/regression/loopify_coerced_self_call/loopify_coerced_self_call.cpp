#include "loopify_coerced_self_call.h"

Nat::EvenT Nat::EvenT_2(uint64_t,
                        const Sig<uint64_t> &h0) { // Precondition: n == (2 * m)
  const auto &[x0] = h0;
  return Sig<uint64_t>::exist((x0 + 1));
}

Nat::EvenT Nat::even_EvenT(uint64_t n) { /// CraneEnter: captures varying
                                         /// parameters for each recursive call.

  struct CraneEnter {
    uint64_t n;
  };

  /// CraneCont_n1: saves [n1], resumes after recursive call, then processes
  /// rest.
  struct CraneCont_n1 {
    uint64_t n1;
  };

  using CraneFrame = std::variant<CraneEnter, CraneCont_n1>;
  Nat::EvenT _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{n});
  /// Loopified even_EvenT: CraneEnter -> CraneCont_n1.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = EvenT_0;
      } else {
        uint64_t n0 = n - 1;
        if (n0 <= 0) {
          throw std::logic_error("absurd case");
        } else {
          uint64_t n1 = n0 - 1;
          _stack.emplace_back(CraneCont_n1{n1});
          _stack.emplace_back(CraneEnter{n1});
        }
      }
    } else {
      auto _f = std::move(std::get<CraneCont_n1>(_frame));
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
uint64_t LoopifyCoercedSelfCall::half(uint64_t n) {
  const auto &_sv = Nat::even_EvenT(n);
  const auto &[x] = _sv;
  return x;
}
