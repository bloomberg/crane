#include "prod_drain.h"

ProdDrain::t ProdDrain::build(uint64_t n, ProdDrain::t acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  ProdDrain::t _loop_acc = std::move(acc);
  while (true) {
    if (n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = n - 1;
      uint64_t _next_n = m;
      _loop_acc = t::n(std::make_pair(std::move(_loop_acc), n));
      n = _next_n;
    }
  }
}

uint64_t ProdDrain::depth(const ProdDrain::t &x) {
  // Explicit stack replaces the non-tail recursion of depth: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    ProdDrain::t x;
  };

  struct _after_depth_in_pair {};

  using _frame = std::variant<_call, _after_depth_in_pair>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const ProdDrain::t &x = _f.x;
      if (std::holds_alternative<typename ProdDrain::t::L>(x.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a0] = std::get<typename ProdDrain::t::N>(x.v());
        const auto &[u, _x] = (*a0);
        _stack.emplace_back(_after_depth_in_pair{});
        _stack.emplace_back(_call{u});
      }
    } else {
      auto _f = std::move(std::get<_after_depth_in_pair>(_popped));
      _stack.pop_back();
      _result = (_result + 1);
    }
  }
  return _result;
}

uint64_t ProdDrain::go(uint64_t n) { return depth(build(n, t::l())); }
