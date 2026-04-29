#include <hof_tree_loopify.h>

__attribute__((pure)) HofTreeLoopify::tree<unsigned int>
HofTreeLoopify::depth_tree(unsigned int n) {
  std::unique_ptr<HofTreeLoopify::tree<unsigned int>> _head{};
  std::unique_ptr<HofTreeLoopify::tree<unsigned int>> *_write = &_head;
  unsigned int _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      *(_write) = std::make_unique<HofTreeLoopify::tree<unsigned int>>(
          tree<unsigned int>::leaf());
      break;
    } else {
      unsigned int m = _loop_n - 1;
      auto _cell = std::make_unique<HofTreeLoopify::tree<unsigned int>>(
          typename tree<unsigned int>::Node(
              nullptr, _loop_n,
              std::make_unique<HofTreeLoopify::tree<unsigned int>>(
                  tree<unsigned int>::leaf())));
      *(_write) = std::move(_cell);
      _write =
          &std::get<typename tree<unsigned int>::Node>((*_write)->v_mut()).d_a0;
      _loop_n = m;
      continue;
    }
  }
  return std::move(*(_head));
}

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int &n,
                                                 unsigned int m) {
  unsigned int _result;
  unsigned int _loop_m = std::move(m);
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      _result = _loop_m;
      break;
    } else {
      unsigned int n0 = _loop_n - 1;
      unsigned int _next_m = (_loop_m + 1);
      unsigned int _next_n = n0;
      _loop_m = std::move(_next_m);
      _loop_n = std::move(_next_n);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int
Nat::tail_addmul(unsigned int r, const unsigned int &n, const unsigned int &m) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_r = std::move(r);
  while (true) {
    if (_loop_n <= 0) {
      _result = _loop_r;
      break;
    } else {
      unsigned int n0 = _loop_n - 1;
      unsigned int _next_n = n0;
      unsigned int _next_r = Nat::tail_add(m, _loop_r);
      _loop_n = std::move(_next_n);
      _loop_r = std::move(_next_r);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::tail_mul(const unsigned int &n,
                                                 const unsigned int &m) {
  return Nat::tail_addmul(0u, n, m);
}

__attribute__((pure)) unsigned int Nat::of_uint_acc(const Uint &d,
                                                    unsigned int acc) {
  unsigned int _result;
  unsigned int _loop_acc = std::move(acc);
  const Uint *_loop_d = &d;
  while (true) {
    if (std::holds_alternative<typename Uint::Nil>(_loop_d->v())) {
      _result = _loop_acc;
      break;
    } else if (std::holds_alternative<typename Uint::D0>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D0>(_loop_d->v());
      unsigned int _next_acc = Nat::tail_mul(10u, _loop_acc);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D1>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D1>(_loop_d->v());
      unsigned int _next_acc = (Nat::tail_mul(10u, _loop_acc) + 1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D2>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D2>(_loop_d->v());
      unsigned int _next_acc = ((Nat::tail_mul(10u, _loop_acc) + 1) + 1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D3>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D3>(_loop_d->v());
      unsigned int _next_acc = (((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D4>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D4>(_loop_d->v());
      unsigned int _next_acc =
          ((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D5>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D5>(_loop_d->v());
      unsigned int _next_acc =
          (((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) + 1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D6>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D6>(_loop_d->v());
      unsigned int _next_acc =
          ((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D7>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D7>(_loop_d->v());
      unsigned int _next_acc =
          (((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1) +
           1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint::D8>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint::D8>(_loop_d->v());
      unsigned int _next_acc =
          ((((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else {
      const auto &[d_a0] = std::get<typename Uint::D9>(_loop_d->v());
      unsigned int _next_acc =
          (((((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1);
      const Uint *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::of_uint(const Uint &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int Nat::of_hex_uint_acc(const Uint0 &d,
                                                        unsigned int acc) {
  unsigned int _result;
  unsigned int _loop_acc = std::move(acc);
  const Uint0 *_loop_d = &d;
  while (true) {
    if (std::holds_alternative<typename Uint0::Nil0>(_loop_d->v())) {
      _result = _loop_acc;
      break;
    } else if (std::holds_alternative<typename Uint0::D10>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D10>(_loop_d->v());
      unsigned int _next_acc = Nat::tail_mul(16u, _loop_acc);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D11>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D11>(_loop_d->v());
      unsigned int _next_acc = (Nat::tail_mul(16u, _loop_acc) + 1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D12>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D12>(_loop_d->v());
      unsigned int _next_acc = ((Nat::tail_mul(16u, _loop_acc) + 1) + 1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D13>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D13>(_loop_d->v());
      unsigned int _next_acc = (((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D14>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D14>(_loop_d->v());
      unsigned int _next_acc =
          ((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D15>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D15>(_loop_d->v());
      unsigned int _next_acc =
          (((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D16>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D16>(_loop_d->v());
      unsigned int _next_acc =
          ((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D17>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D17>(_loop_d->v());
      unsigned int _next_acc =
          (((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D18>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D18>(_loop_d->v());
      unsigned int _next_acc =
          ((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::D19>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::D19>(_loop_d->v());
      unsigned int _next_acc =
          (((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::Da>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::Da>(_loop_d->v());
      unsigned int _next_acc =
          ((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::Db>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::Db>(_loop_d->v());
      unsigned int _next_acc =
          (((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::Dc>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::Dc>(_loop_d->v());
      unsigned int _next_acc =
          ((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::Dd>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::Dd>(_loop_d->v());
      unsigned int _next_acc =
          (((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else if (std::holds_alternative<typename Uint0::De>(_loop_d->v())) {
      const auto &[d_a0] = std::get<typename Uint0::De>(_loop_d->v());
      unsigned int _next_acc =
          ((((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1);
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    } else {
      const auto &[d_a0] = std::get<typename Uint0::Df>(_loop_d->v());
      unsigned int _next_acc =
          (((((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) +
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
      const Uint0 *_next_d = d_a0.get();
      _loop_acc = std::move(_next_acc);
      _loop_d = std::move(_next_d);
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[d_u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(d_u);
  } else {
    const auto &[d_u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(d_u);
  }
}
