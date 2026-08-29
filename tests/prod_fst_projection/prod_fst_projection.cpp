#include "prod_fst_projection.h"

ProdFstProjection::t ProdFstProjection::build(uint64_t n,
                                              ProdFstProjection::t acc) {
  ProdFstProjection::t _loop_acc = std::move(acc);
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

uint64_t ProdFstProjection::depth(
    const ProdFstProjection::t
        &x) { /// _Enter: captures varying parameters for each recursive call.

  struct _Enter {
    ProdFstProjection::t x;
  };

  /// _Resume_N: resumes after recursive call with _result.
  struct _Resume_N {};

  using _Frame = std::variant<_Enter, _Resume_N>;
  uint64_t _result{};
  crane::small_vector<_Frame> _stack;
  _stack.emplace_back(_Enter{x});
  /// Loopified depth: _Enter -> _Resume_N.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      const ProdFstProjection::t &x = std::move(_f.x);
      if (std::holds_alternative<typename ProdFstProjection::t::L>(x.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0] = std::get<typename ProdFstProjection::t::N>(x.v());
        _stack.emplace_back(_Resume_N{});
        _stack.emplace_back(_Enter{(*a0).first});
      }
    } else {
      auto _f = std::move(std::get<_Resume_N>(_frame));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t ProdFstProjection::go(uint64_t n) { return depth(build(n, t::l())); }
