#include <loopify_generators.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Consolidated list generator functions.
/// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::cycle(const unsigned int n,
                         const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::nil();
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{l});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = _f._s0->app(_result); }},
               _frame);
  }
  return _result;
}

/// zip_longest l1 l2 default zips, using default for missing elements.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyGenerators::zip_longest_aux(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2, const unsigned int default0,
    const unsigned int fuel) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  unsigned int _loop_fuel = fuel;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<std::pair<unsigned int, unsigned int>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
        } else {
          _head = List<std::pair<unsigned int, unsigned int>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil _args) {
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args0) {
                          if (_last) {
                            std::get<typename List<
                                std::pair<unsigned int, unsigned int>>::Cons>(
                                _last->v_mut())
                                .d_a1 = List<
                                std::pair<unsigned int, unsigned int>>::nil();
                          } else {
                            _head = List<
                                std::pair<unsigned int, unsigned int>>::nil();
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons _args0) {
                          auto _cell =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(default0, _args0.d_a0),
                                  nullptr);
                          if (_last) {
                            std::get<typename List<
                                std::pair<unsigned int, unsigned int>>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          unsigned int _next_fuel = f;
                          std::shared_ptr<List<unsigned int>> _next_l2 =
                              _args0.d_a1;
                          std::shared_ptr<List<unsigned int>> _next_l1 =
                              List<unsigned int>::nil();
                          _loop_fuel = std::move(_next_fuel);
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        }},
                    _loop_l2->v());
              },
              [&](const typename List<unsigned int>::Cons _args) {
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args0) {
                          auto _cell =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(_args.d_a0, default0),
                                  nullptr);
                          if (_last) {
                            std::get<typename List<
                                std::pair<unsigned int, unsigned int>>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          unsigned int _next_fuel = f;
                          std::shared_ptr<List<unsigned int>> _next_l2 =
                              List<unsigned int>::nil();
                          std::shared_ptr<List<unsigned int>> _next_l1 =
                              _args.d_a1;
                          _loop_fuel = std::move(_next_fuel);
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        },
                        [&](const typename List<unsigned int>::Cons _args0) {
                          auto _cell =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(_args.d_a0, _args0.d_a0),
                                  nullptr);
                          if (_last) {
                            std::get<typename List<
                                std::pair<unsigned int, unsigned int>>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          unsigned int _next_fuel = f;
                          std::shared_ptr<List<unsigned int>> _next_l2 =
                              _args0.d_a1;
                          std::shared_ptr<List<unsigned int>> _next_l1 =
                              _args.d_a1;
                          _loop_fuel = std::move(_next_fuel);
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        }},
                    _loop_l2->v());
              }},
          _loop_l1->v());
    }
  }
  return _head;
}

__attribute__((pure)) unsigned int
LoopifyGenerators::len_impl(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_result + 1); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyGenerators::zip_longest(const std::shared_ptr<List<unsigned int>> &l1,
                               const std::shared_ptr<List<unsigned int>> &l2,
                               const unsigned int default0) {
  return zip_longest_aux(l1, l2, default0, (len_impl(l1) + len_impl(l2)));
}

/// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::build_list_fuel(const unsigned int fuel,
                                   const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            const unsigned int fuel = _f.fuel;
                            if (fuel <= 0) {
                              _result = List<unsigned int>::nil();
                            } else {
                              unsigned int f = fuel - 1;
                              if (n <= 0) {
                                _result = List<unsigned int>::nil();
                              } else {
                                unsigned int n_ = n - 1;
                                if (n_ <= 0) {
                                  _result = List<unsigned int>::cons(
                                      1u, List<unsigned int>::nil());
                                } else {
                                  unsigned int _x = n_ - 1;
                                  unsigned int half = Nat::div(n_, 2u);
                                  _stack.push_back(_Call1{n_});
                                  _stack.push_back(_Enter{std::move(half), f});
                                }
                              }
                            }
                          },
                          [&](_Call1 _f) {
                            unsigned int n_ = _f._s0;
                            std::shared_ptr<List<unsigned int>> half_result =
                                _result;
                            _result = half_result->app(
                                List<unsigned int>::cons(n_, half_result));
                          }},
               _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyGenerators::build_list(const unsigned int n) {
  return build_list_fuel(100u, n);
}

/// take n l returns first n elements.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::take(const unsigned int n,
                        const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if (_loop_n == 0u) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
                }
                _continue = false;
              } else {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_n =
                    (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }
            }},
        _loop_l->v());
  }
  return _head;
}

/// repeat x n creates list with n copies of x.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::repeat(const unsigned int x, const unsigned int n) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      {
        auto _cell = List<unsigned int>::cons(x, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
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

/// Helper: replicate single element n times.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::replicate_single(const unsigned int x,
                                    const unsigned int n) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              List<unsigned int>::nil();
        } else {
          _head = List<unsigned int>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      {
        auto _cell = List<unsigned int>::cons(x, nullptr);
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
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

/// replicate_each n l replicates each element n times: replicate_each 2 1,2 ->
/// 1,1,2,2.
std::shared_ptr<List<unsigned int>> LoopifyGenerators::replicate_each(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(replicate_single(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const unsigned int &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void { _result = List<unsigned int>::nil(); },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(
                            _Call1{replicate_single(_args.d_a0, n)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  std::pair<unsigned int, unsigned int> _result;
  unsigned int _loop_u = u;
  unsigned int _loop_q = q;
  unsigned int _loop_x = x;
  bool _continue = true;
  while (_continue) {
    if (_loop_x <= 0) {
      {
        _result = std::make_pair(_loop_q, _loop_u);
        _continue = false;
      }
    } else {
      unsigned int x_ = _loop_x - 1;
      if (_loop_u <= 0) {
        {
          unsigned int _next_u = y;
          unsigned int _next_q = (_loop_q + 1);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_q = std::move(_next_q);
          _loop_x = std::move(_next_x);
          continue;
        }
      } else {
        unsigned int u_ = _loop_u - 1;
        {
          unsigned int _next_u = std::move(u_);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_x = std::move(_next_x);
          continue;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
