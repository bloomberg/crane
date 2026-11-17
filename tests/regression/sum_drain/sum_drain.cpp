#include "sum_drain.h"

SumDrain::t SumDrain::build(uint64_t n, SumDrain::t acc) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
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

uint64_t SumDrain::depth(const SumDrain::t &x) {
  // Explicit stack replaces the non-tail recursion of depth: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const SumDrain::t *x;
  };

  struct _after_depth_in_Inr {};

  using _frame = std::variant<_call, _after_depth_in_Inr>;
  uint64_t _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{&x});
  while (!_stack.empty()) {
    _frame _popped = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      const SumDrain::t &x = *_f.x;
      const auto &[a0] = std::get<typename SumDrain::t::N>(x.v());
      auto &&_sv0 = *a0;
      if (std::holds_alternative<typename Sum<uint64_t, SumDrain::t>::Inl>(
              _sv0.v())) {
        _result = UINT64_C(0);
      } else {
        const auto &[a00] =
            std::get<typename Sum<uint64_t, SumDrain::t>::Inr>(_sv0.v());
        _stack.emplace_back(_after_depth_in_Inr{});
        _stack.emplace_back(_call{&a00});
      }
    } else {
      auto _f = std::move(std::get<_after_depth_in_Inr>(_popped));
      _result = (std::move(_result) + 1);
    }
  }
  return _result;
}

uint64_t SumDrain::go(uint64_t n) {
  return depth(build(n, t::n(Sum<uint64_t, SumDrain::t>::inl(UINT64_C(0)))));
}
