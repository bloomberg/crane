#include "prod_drain.h"

ProdDrain::t ProdDrain::build(uint64_t n, ProdDrain::t acc) {
  ProdDrain::t _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t _next_n = m;
      _loop_acc = t::n(std::make_pair(std::move(_loop_acc), _loop_n));
      _loop_n = _next_n;
    }
  }
}

uint64_t ProdDrain::depth(
    const ProdDrain::t &x) { /// CraneEnter: captures varying parameters for
                             /// each recursive call.

  struct CraneEnter {
    ProdDrain::t x;
  };

  /// CraneCont_u: resumes after recursive call, then processes rest.
  struct CraneCont_u {};

  using CraneFrame = std::variant<CraneEnter, CraneCont_u>;
  uint64_t _result{};
  crane::small_vector<CraneFrame> _stack;
  _stack.emplace_back(CraneEnter{x});
  /// Loopified depth: CraneEnter -> CraneCont_u.
  while (!_stack.empty()) {
    CraneFrame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<CraneEnter>(_frame)) {
      auto _f = std::move(std::get<CraneEnter>(_frame));
      const ProdDrain::t &x = std::move(_f.x);
      if (std::holds_alternative<typename ProdDrain::t::L>(x.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0] = std::get<typename ProdDrain::t::N>(x.v());
        const auto &[u, _x] = (*a0);
        _stack.emplace_back(CraneCont_u{});
        _stack.emplace_back(CraneEnter{u});
      }
    } else {
      auto _f = std::move(std::get<CraneCont_u>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t ProdDrain::go(uint64_t n) { return depth(build(n, t::l())); }
