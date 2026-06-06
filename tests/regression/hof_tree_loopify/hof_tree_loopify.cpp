#include "hof_tree_loopify.h"

HofTreeLoopify::tree<uint64_t>
HofTreeLoopify::depth_tree(uint64_t n) { /// _Enter: captures varying parameters
                                         /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_m: saves [_s0, n], resumes after recursive call with _result.
  struct _Resume_m {
    std::decay_t<decltype(tree<uint64_t>::leaf())> _s0;
    uint64_t n;
  };

  using _Frame = std::variant<_Enter, _Resume_m>;
  HofTreeLoopify::tree<uint64_t> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified depth_tree: _Enter -> _Resume_m.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = tree<uint64_t>::leaf();
      } else {
        uint64_t m = n - 1;
        _stack.emplace_back(_Resume_m{tree<uint64_t>::leaf(), n});
        _stack.emplace_back(_Enter{m});
      }
    } else {
      auto _f = std::move(std::get<_Resume_m>(_frame));
      _result = tree<uint64_t>::node(std::move(_result), _f.n, _f._s0);
    }
  }
  return _result;
}

uint64_t Nat::tail_add(uint64_t n, uint64_t m) {
  uint64_t _loop_m = std::move(m);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_m;
    } else {
      uint64_t n0 = _loop_n - 1;
      _loop_m = (_loop_m + 1);
      _loop_n = n0;
    }
  }
}

uint64_t Nat::tail_addmul(uint64_t r, uint64_t n, uint64_t m) {
  uint64_t _loop_n = std::move(n);
  uint64_t _loop_r = std::move(r);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_r;
    } else {
      uint64_t n0 = _loop_n - 1;
      _loop_n = n0;
      _loop_r = Nat::tail_add(m, _loop_r);
    }
  }
}

uint64_t Nat::tail_mul(uint64_t n, uint64_t m) {
  return Nat::tail_addmul(UINT64_C(0), n, m);
}

uint64_t Nat::of_uint_acc(const Uint &d, uint64_t acc) {
  uint64_t _loop_acc = std::move(acc);
  const Uint *_loop_d = &d;
  while (true) {
    if (std::holds_alternative<typename Uint::Nil>(_loop_d->v())) {
      return _loop_acc;
    } else if (std::holds_alternative<typename Uint::D0>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D0>(_loop_d->v());
      _loop_acc = Nat::tail_mul(UINT64_C(10), _loop_acc);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D1>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D1>(_loop_d->v());
      _loop_acc = (Nat::tail_mul(UINT64_C(10), _loop_acc) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D2>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D2>(_loop_d->v());
      _loop_acc = ((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D3>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D3>(_loop_d->v());
      _loop_acc = (((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D4>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D4>(_loop_d->v());
      _loop_acc =
          ((((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D5>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D5>(_loop_d->v());
      _loop_acc =
          (((((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1) + 1) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D6>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D6>(_loop_d->v());
      _loop_acc =
          ((((((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1) + 1) + 1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D7>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D7>(_loop_d->v());
      _loop_acc =
          (((((((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint::D8>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint::D8>(_loop_d->v());
      _loop_acc =
          ((((((((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else {
      const auto &[a0] = std::get<typename Uint::D9>(_loop_d->v());
      _loop_acc =
          (((((((((Nat::tail_mul(UINT64_C(10), _loop_acc) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    }
  }
}

uint64_t Nat::of_uint(const Uint &d) {
  return Nat::of_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_hex_uint_acc(const Uint0 &d, uint64_t acc) {
  uint64_t _loop_acc = std::move(acc);
  const Uint0 *_loop_d = &d;
  while (true) {
    if (std::holds_alternative<typename Uint0::Nil0>(_loop_d->v())) {
      return _loop_acc;
    } else if (std::holds_alternative<typename Uint0::D10>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D10>(_loop_d->v());
      _loop_acc = Nat::tail_mul(UINT64_C(16), _loop_acc);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D11>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D11>(_loop_d->v());
      _loop_acc = (Nat::tail_mul(UINT64_C(16), _loop_acc) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D12>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D12>(_loop_d->v());
      _loop_acc = ((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D13>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D13>(_loop_d->v());
      _loop_acc = (((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D14>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D14>(_loop_d->v());
      _loop_acc =
          ((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D15>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D15>(_loop_d->v());
      _loop_acc =
          (((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) + 1) + 1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D16>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D16>(_loop_d->v());
      _loop_acc =
          ((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) + 1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D17>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D17>(_loop_d->v());
      _loop_acc =
          (((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D18>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D18>(_loop_d->v());
      _loop_acc =
          ((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::D19>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::D19>(_loop_d->v());
      _loop_acc =
          (((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::Da>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::Da>(_loop_d->v());
      _loop_acc =
          ((((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::Db>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::Db>(_loop_d->v());
      _loop_acc =
          (((((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::Dc>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::Dc>(_loop_d->v());
      _loop_acc =
          ((((((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::Dd>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::Dd>(_loop_d->v());
      _loop_acc =
          (((((((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else if (std::holds_alternative<typename Uint0::De>(_loop_d->v())) {
      const auto &[a0] = std::get<typename Uint0::De>(_loop_d->v());
      _loop_acc =
          ((((((((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    } else {
      const auto &[a0] = std::get<typename Uint0::Df>(_loop_d->v());
      _loop_acc =
          (((((((((((((((Nat::tail_mul(UINT64_C(16), _loop_acc) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      _loop_d = a0.get();
    }
  }
}

uint64_t Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(u);
  } else {
    const auto &[u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(u);
  }
}
