#include <hof_tree_loopify.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<HofTreeLoopify::tree<unsigned int>>
HofTreeLoopify::depth_tree(const unsigned int n) {
  std::shared_ptr<HofTreeLoopify::tree<unsigned int>> _head{};
  std::shared_ptr<HofTreeLoopify::tree<unsigned int>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename tree<unsigned int>::Node>(_last->v_mut()).d_a0 =
              tree<unsigned int>::leaf();
        } else {
          _head = tree<unsigned int>::leaf();
        }
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      {
        auto _cell = tree<unsigned int>::node(nullptr, _loop_n,
                                              tree<unsigned int>::leaf());
        if (_last) {
          std::get<typename tree<unsigned int>::Node>(_last->v_mut()).d_a0 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_n = m;
        continue;
      }
    }
  }
  return _head;
}

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int n,
                                                 const unsigned int m) {
  unsigned int _result;
  unsigned int _loop_m = m;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = _loop_m;
        _continue = false;
      }
    } else {
      unsigned int n0 = _loop_n - 1;
      {
        unsigned int _next_m = (_loop_m + 1);
        unsigned int _next_n = n0;
        _loop_m = std::move(_next_m);
        _loop_n = std::move(_next_n);
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::tail_addmul(const unsigned int r,
                                                    const unsigned int n,
                                                    const unsigned int m) {
  unsigned int _result;
  unsigned int _loop_n = n;
  unsigned int _loop_r = r;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = _loop_r;
        _continue = false;
      }
    } else {
      unsigned int n0 = _loop_n - 1;
      {
        unsigned int _next_n = n0;
        unsigned int _next_r = Nat::tail_add(m, _loop_r);
        _loop_n = std::move(_next_n);
        _loop_r = std::move(_next_r);
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::tail_mul(const unsigned int n,
                                                 const unsigned int m) {
  return Nat::tail_addmul(0u, n, m);
}

__attribute__((pure)) unsigned int
Nat::of_uint_acc(const std::shared_ptr<Uint> &d, const unsigned int acc) {
  unsigned int _result;
  unsigned int _loop_acc = acc;
  std::shared_ptr<Uint> _loop_d = d;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename Uint::Nil &) {
              _result = _loop_acc;
              _continue = false;
            },
            [&](const typename Uint::D0 &_args) {
              unsigned int _next_acc = Nat::tail_mul(10u, _loop_acc);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D1 &_args) {
              unsigned int _next_acc = (Nat::tail_mul(10u, _loop_acc) + 1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D2 &_args) {
              unsigned int _next_acc =
                  ((Nat::tail_mul(10u, _loop_acc) + 1) + 1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D3 &_args) {
              unsigned int _next_acc =
                  (((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D4 &_args) {
              unsigned int _next_acc =
                  ((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D5 &_args) {
              unsigned int _next_acc =
                  (((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) + 1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D6 &_args) {
              unsigned int _next_acc =
                  ((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) + 1) +
                   1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D7 &_args) {
              unsigned int _next_acc =
                  (((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D8 &_args) {
              unsigned int _next_acc =
                  ((((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint::D9 &_args) {
              unsigned int _next_acc =
                  (((((((((Nat::tail_mul(10u, _loop_acc) + 1) + 1) + 1) + 1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            }},
        _loop_d->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int
Nat::of_uint(const std::shared_ptr<Uint> &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc) {
  unsigned int _result;
  unsigned int _loop_acc = acc;
  std::shared_ptr<Uint0> _loop_d = d;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename Uint0::Nil0 &) {
              _result = _loop_acc;
              _continue = false;
            },
            [&](const typename Uint0::D10 &_args) {
              unsigned int _next_acc = Nat::tail_mul(16u, _loop_acc);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D11 &_args) {
              unsigned int _next_acc = (Nat::tail_mul(16u, _loop_acc) + 1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D12 &_args) {
              unsigned int _next_acc =
                  ((Nat::tail_mul(16u, _loop_acc) + 1) + 1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D13 &_args) {
              unsigned int _next_acc =
                  (((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D14 &_args) {
              unsigned int _next_acc =
                  ((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D15 &_args) {
              unsigned int _next_acc =
                  (((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D16 &_args) {
              unsigned int _next_acc =
                  ((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) + 1) +
                   1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D17 &_args) {
              unsigned int _next_acc =
                  (((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D18 &_args) {
              unsigned int _next_acc =
                  ((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::D19 &_args) {
              unsigned int _next_acc =
                  (((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::Da &_args) {
              unsigned int _next_acc =
                  ((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::Db &_args) {
              unsigned int _next_acc =
                  (((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) + 1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::Dc &_args) {
              unsigned int _next_acc =
                  ((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1);
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::Dd &_args) {
              unsigned int _next_acc =
                  (((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) +
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
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::De &_args) {
              unsigned int _next_acc =
                  ((((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) +
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
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            },
            [&](const typename Uint0::Df &_args) {
              unsigned int _next_acc =
                  (((((((((((((((Nat::tail_mul(16u, _loop_acc) + 1) + 1) + 1) +
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
              std::shared_ptr<Uint0> _next_d = _args.d_a0;
              _loop_acc = std::move(_next_acc);
              _loop_d = std::move(_next_d);
            }},
        _loop_d->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint(const std::shared_ptr<Uint0> &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_num_uint(const std::shared_ptr<Uint1> &d) {
  return std::visit(
      Overloaded{[](const typename Uint1::UIntDecimal &_args) -> unsigned int {
                   return Nat::of_uint(_args.d_u);
                 },
                 [](const typename Uint1::UIntHexadecimal &_args)
                     -> unsigned int { return Nat::of_hex_uint(_args.d_u); }},
      d->v());
}
