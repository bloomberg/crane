#include <loopify_algorithms.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

/// Consolidated UNIQUE list/sequence algorithms.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::len_impl(const std::shared_ptr<List<unsigned int>> &l) {
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

/// sieve l Sieve of Eratosthenes - filters out multiples.
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::sieve_fuel(const unsigned int fuel,
                              std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              std::move(_loop_l);
        } else {
          _head = std::move(_loop_l);
        }
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
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
                std::function<std::shared_ptr<List<unsigned int>>(
                    unsigned int, std::shared_ptr<List<unsigned int>>)>
                    filter_multiples;
                filter_multiples = [&](unsigned int p,
                                       std::shared_ptr<List<unsigned int>> rest)
                    -> std::shared_ptr<List<unsigned int>> {
                  struct _Enter {
                    std::shared_ptr<List<unsigned int>> rest;
                    unsigned int p;
                  };
                  struct _Call1 {
                    decltype(std::declval<
                                 const typename List<unsigned int>::Cons &>()
                                 .d_a0) _s0;
                  };
                  using _Frame = std::variant<_Enter, _Call1>;
                  std::shared_ptr<List<unsigned int>> _result{};
                  std::vector<_Frame> _stack;
                  _stack.push_back(_Enter{rest, p});
                  while (!_stack.empty()) {
                    _Frame _frame = std::move(_stack.back());
                    _stack.pop_back();
                    std::visit(
                        Overloaded{
                            [&](_Enter _f) {
                              std::shared_ptr<List<unsigned int>> rest =
                                  _f.rest;
                              unsigned int p = _f.p;
                              std::visit(
                                  Overloaded{
                                      [&](const typename List<unsigned int>::Nil
                                              _args0) -> void {
                                        _result = List<unsigned int>::nil();
                                      },
                                      [&](const typename List<
                                          unsigned int>::Cons _args0) -> void {
                                        if ((_args0.d_a0 % p) == 0u) {
                                          _stack.push_back(_Enter{
                                              _args0.d_a1, std::move(p)});
                                        } else {
                                          _stack.push_back(_Call1{_args0.d_a0});
                                          _stack.push_back(_Enter{
                                              _args0.d_a1, std::move(p)});
                                        }
                                      }},
                                  rest->v());
                            },
                            [&](_Call1 _f) {
                              _result =
                                  List<unsigned int>::cons(_f._s0, _result);
                            }},
                        _frame);
                  }
                  return _result;
                };
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l =
                    filter_multiples(_args.d_a0, _args.d_a1);
                unsigned int _next_fuel = std::move(f);
                _loop_l = std::move(_next_l);
                _loop_fuel = std::move(_next_fuel);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::sieve(const std::shared_ptr<List<unsigned int>> &l) {
  return sieve_fuel(len_impl(l), l);
}

/// run_length_encode l encodes consecutive runs: 1,1,2,3,3,3 ->
/// (1,2),(2,1),(3,3).
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyAlgorithms::run_length_encode(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
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
                          -> void {
                        _result =
                            List<std::pair<unsigned int, unsigned int>>::nil();
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Nil _args0)
                          -> void {
                        _result =
                            List<std::pair<unsigned int, unsigned int>>::cons(
                                std::make_pair(_args.d_a0, 1u),
                                List<std::pair<unsigned int,
                                               unsigned int>>::nil());
                      },
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Cons _args0)
                          -> void {
                        unsigned int y = _args0.d_a0.first;
                        unsigned int n = _args0.d_a0.second;
                        if (_args.d_a0 == y) {
                          _result =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(y, (n + 1)), _args0.d_a1);
                        } else {
                          _result =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(_args.d_a0, 1u),
                                  List<std::pair<unsigned int, unsigned int>>::
                                      cons(std::make_pair(y, n), _args0.d_a1));
                        }
                      }},
                  _result->v());
            }},
        _frame);
  }
  return _result;
}

/// prefix_sums acc l cumulative sums: 1,2,3 with acc=0 -> 0,1,3,6.
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::prefix_sums(const unsigned int acc,
                               const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::cons(std::move(_loop_acc),
                                                     List<unsigned int>::nil());
              } else {
                _head = List<unsigned int>::cons(std::move(_loop_acc),
                                                 List<unsigned int>::nil());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              auto _cell = List<unsigned int>::cons(_loop_acc, nullptr);
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
              unsigned int _next_acc = (_loop_acc + _args.d_a0);
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _head;
}

/// differences l consecutive differences: 5,3,8,2 -> -2,5,-6.
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::differences(const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
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
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = List<unsigned int>::nil();
                        } else {
                          _head = List<unsigned int>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        auto _cell = List<unsigned int>::cons(
                            (((_args0.d_a0 - _args.d_a0) > _args0.d_a0
                                  ? 0
                                  : (_args0.d_a0 - _args.d_a0))),
                            nullptr);
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// rotate_left n l rotates list left by n positions.
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::rotate_left_fuel(const unsigned int fuel,
                                    const unsigned int n,
                                    std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = std::move(_loop_l);
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      if (_loop_n <= 0u) {
        {
          _result = _loop_l;
          _continue = false;
        }
      } else {
        std::visit(
            Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                         _result = List<unsigned int>::nil();
                         _continue = false;
                       },
                       [&](const typename List<unsigned int>::Cons _args) {
                         std::shared_ptr<List<unsigned int>> _next_l =
                             _args.d_a1->app(List<unsigned int>::cons(
                                 _args.d_a0, List<unsigned int>::nil()));
                         unsigned int _next_n =
                             (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                         unsigned int _next_fuel = std::move(f);
                         _loop_l = std::move(_next_l);
                         _loop_n = std::move(_next_n);
                         _loop_fuel = std::move(_next_fuel);
                       }},
            _loop_l->v());
      }
    }
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::rotate_left(const unsigned int n,
                               const std::shared_ptr<List<unsigned int>> &l) {
  return rotate_left_fuel(n, n, l);
}

/// nub l removes ALL duplicates (not just consecutive): 1,2,1,3,2 -> 1,2,3.
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::nub_aux(const std::shared_ptr<List<unsigned int>> &l,
                           const unsigned int fuel) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_fuel = fuel;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
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
      unsigned int f = _loop_fuel - 1;
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
                std::function<std::shared_ptr<List<unsigned int>>(
                    unsigned int, std::shared_ptr<List<unsigned int>>)>
                    filter_out;
                filter_out = [&](unsigned int val,
                                 std::shared_ptr<List<unsigned int>> rest)
                    -> std::shared_ptr<List<unsigned int>> {
                  struct _Enter {
                    std::shared_ptr<List<unsigned int>> rest;
                    unsigned int val;
                  };
                  struct _Call1 {
                    decltype(std::declval<
                                 const typename List<unsigned int>::Cons &>()
                                 .d_a0) _s0;
                  };
                  using _Frame = std::variant<_Enter, _Call1>;
                  std::shared_ptr<List<unsigned int>> _result{};
                  std::vector<_Frame> _stack;
                  _stack.push_back(_Enter{rest, val});
                  while (!_stack.empty()) {
                    _Frame _frame = std::move(_stack.back());
                    _stack.pop_back();
                    std::visit(
                        Overloaded{
                            [&](_Enter _f) {
                              std::shared_ptr<List<unsigned int>> rest =
                                  _f.rest;
                              unsigned int val = _f.val;
                              std::visit(
                                  Overloaded{
                                      [&](const typename List<unsigned int>::Nil
                                              _args0) -> void {
                                        _result = List<unsigned int>::nil();
                                      },
                                      [&](const typename List<
                                          unsigned int>::Cons _args0) -> void {
                                        if (val == _args0.d_a0) {
                                          _stack.push_back(_Enter{
                                              _args0.d_a1, std::move(val)});
                                        } else {
                                          _stack.push_back(_Call1{_args0.d_a0});
                                          _stack.push_back(_Enter{
                                              _args0.d_a1, std::move(val)});
                                        }
                                      }},
                                  rest->v());
                            },
                            [&](_Call1 _f) {
                              _result =
                                  List<unsigned int>::cons(_f._s0, _result);
                            }},
                        _frame);
                  }
                  return _result;
                };
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                unsigned int _next_fuel = f;
                std::shared_ptr<List<unsigned int>> _next_l =
                    filter_out(_args.d_a0, _args.d_a1);
                _loop_fuel = std::move(_next_fuel);
                _loop_l = std::move(_next_l);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::nub(const std::shared_ptr<List<unsigned int>> &l) {
  return nub_aux(l, len_impl(l));
}

/// Internal helpers for palindrome check.
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::rev_impl(std::shared_ptr<List<unsigned int>> acc,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  std::shared_ptr<List<unsigned int>> _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                            _result = std::move(_loop_acc);
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args) {
                            std::shared_ptr<List<unsigned int>> _next_l =
                                _args.d_a1;
                            std::shared_ptr<List<unsigned int>> _next_acc =
                                List<unsigned int>::cons(_args.d_a0,
                                                         std::move(_loop_acc));
                            _loop_l = std::move(_next_l);
                            _loop_acc = std::move(_next_acc);
                          }},
               _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyAlgorithms::list_eq_impl(const std::shared_ptr<List<unsigned int>> &l1,
                                const std::shared_ptr<List<unsigned int>> &l2) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = std::visit(
                  Overloaded{[](const typename List<unsigned int>::Nil _args0)
                                 -> bool { return true; },
                             [](const typename List<unsigned int>::Cons _args0)
                                 -> bool { return false; }},
                  _loop_l2->v());
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _result = false;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          std::shared_ptr<List<unsigned int>> _next_l2 =
                              _args0.d_a1;
                          std::shared_ptr<List<unsigned int>> _next_l1 =
                              _args.d_a1;
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        } else {
                          _result = false;
                          _continue = false;
                        }
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _result;
}

/// is_palindrome l checks if list reads same forwards and backwards.
__attribute__((pure)) bool
LoopifyAlgorithms::is_palindrome(const std::shared_ptr<List<unsigned int>> &l) {
  return list_eq_impl(l, rev_impl(List<unsigned int>::nil(), l));
}

/// windows n l sliding windows of size n: windows 2 1,2,3,4 ->
/// [1,2],[2,3],[3,4].
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::take_impl(const unsigned int k,
                             const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_k = k;
  bool _continue = true;
  while (_continue) {
    if (_loop_k <= 0) {
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
      unsigned int m = _loop_k - 1;
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
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_k = m;
                _loop_l = std::move(_next_l);
                _loop_k = std::move(_next_k);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyAlgorithms::windows_aux(const unsigned int n,
                               std::shared_ptr<List<unsigned int>> l,
                               const unsigned int fuel) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  unsigned int _loop_fuel = fuel;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
        } else {
          _head = List<std::shared_ptr<List<unsigned int>>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil _args) {
                if (_last) {
                  std::get<
                      typename List<std::shared_ptr<List<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = List<std::shared_ptr<List<unsigned int>>>::nil();
                } else {
                  _head = List<std::shared_ptr<List<unsigned int>>>::nil();
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                if (len_impl(_loop_l) < n) {
                  if (_last) {
                    std::get<typename List<
                        std::shared_ptr<List<unsigned int>>>::Cons>(
                        _last->v_mut())
                        .d_a1 =
                        List<std::shared_ptr<List<unsigned int>>>::nil();
                  } else {
                    _head = List<std::shared_ptr<List<unsigned int>>>::nil();
                  }
                  _continue = false;
                } else {
                  auto _cell = List<std::shared_ptr<List<unsigned int>>>::cons(
                      take_impl(n, std::move(_loop_l)), nullptr);
                  if (_last) {
                    std::get<typename List<
                        std::shared_ptr<List<unsigned int>>>::Cons>(
                        _last->v_mut())
                        .d_a1 = _cell;
                  } else {
                    _head = _cell;
                  }
                  _last = _cell;
                  unsigned int _next_fuel = f;
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  _loop_fuel = std::move(_next_fuel);
                  _loop_l = std::move(_next_l);
                }
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyAlgorithms::windows(const unsigned int n,
                           std::shared_ptr<List<unsigned int>> l) {
  return windows_aux(n, l, (len_impl(l) + 1));
}

/// sliding_pairs l returns consecutive pairs: 1,2,3,4 -> (1,2),(2,3),(3,4).
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyAlgorithms::sliding_pairs(const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              if (_last) {
                std::get<
                    typename List<std::pair<unsigned int, unsigned int>>::Cons>(
                    _last->v_mut())
                    .d_a1 = List<std::pair<unsigned int, unsigned int>>::nil();
              } else {
                _head = List<std::pair<unsigned int, unsigned int>>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
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
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// max_prefix_sum l maximum sum of prefix (Kadane-like pattern).
__attribute__((pure)) unsigned int LoopifyAlgorithms::max_prefix_sum(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

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
                               _stack.push_back(_Call1{_args});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     const typename List<unsigned int>::Cons _args = _f._s0;
                     unsigned int rest = _result;
                     unsigned int sum = (_args.d_a0 + rest);
                     if (rest == 0u) {
                       _result = 0u;
                     } else {
                       if (rest < sum) {
                         _result = std::move(sum);
                       } else {
                         _result = std::move(rest);
                       }
                     }
                   }},
        _frame);
  }
  return _result;
}

/// weighted_sum i l computes weighted sum with increasing index.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::weighted_sum(const unsigned int i,
                                const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int i;
  };

  struct _Call1 {
    decltype((
        std::declval<const unsigned int &>() *
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, i});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int i = _f.i;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{(i * _args.d_a0)});
                               _stack.push_back(_Enter{_args.d_a1, (i + 1)});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// step_sum l sums with conditional doubling for odd numbers.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::step_sum(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

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
                               unsigned int contribution;
                               if ((_args.d_a0 % 2u) == 0u) {
                                 contribution = _args.d_a0;
                               } else {
                                 contribution = (_args.d_a0 * 2u);
                               }
                               _stack.push_back(
                                   _Call1{std::move(contribution)});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// Helper: get head with default value.
__attribute__((pure)) unsigned int
LoopifyAlgorithms::head_nat(const unsigned int d,
                            const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                   -> unsigned int { return std::move(d); },
                               [](const typename List<unsigned int>::Cons _args)
                                   -> unsigned int { return _args.d_a0; }},
                    l->v());
}

/// suffix_sums l computes suffix sums (reverse of prefix sums).
std::shared_ptr<List<unsigned int>>
LoopifyAlgorithms::suffix_sums(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> rest = _result;
              _result = List<unsigned int>::cons(
                  (_args.d_a0 + head_nat(0u, rest)), rest);
            }},
        _frame);
  }
  return _result;
}
