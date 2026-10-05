#include "sum_drain.h"

SumDrain::t SumDrain::build(uint64_t n, SumDrain::t acc) {
  SumDrain::t _loop_acc = std::move(acc);
  uint64_t _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      _loop_acc = t::n(Sum<uint64_t, SumDrain::t>::inr(std::move(_loop_acc)));
      _loop_n = m;
    }
  }
}

uint64_t
SumDrain::depth(const SumDrain::t &x) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

  struct CraneEnter {
    SumDrain::t x;
  };

  /// CraneCont_Inr: resumes after recursive call, then processes rest.
  struct CraneCont_Inr {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_Inr>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{x});
  /// Loopified depth: CraneEnter -> CraneCont_Inr.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const SumDrain::t &x = std::move(_f.x);
      const auto &[a0] = std::get<typename SumDrain::t::N>(x.v());
      auto &&_sv0 = *a0;
      if (std::holds_alternative<typename Sum<uint64_t, SumDrain::t>::Inl>(
              _sv0.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a00] =
            std::get<typename Sum<uint64_t, SumDrain::t>::Inr>(_sv0.v());
        _stack.emplace_back(CraneCont_Inr{});
        _stack.emplace_back(CraneEnter{a00});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_Inr>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t SumDrain::go(uint64_t n) {
  return depth(build(n, t::n(Sum<uint64_t, SumDrain::t>::inl(UINT64_C(0)))));
}
