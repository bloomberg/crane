#include <loopify_lists.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
/// range start count generates start, start+1, ..., start+count-1.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::range(const unsigned int start, const unsigned int count0) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  unsigned int _loop_count0 = count0;
  unsigned int _loop_start = start;
  bool _continue = true;
  while (_continue) {
    if (_loop_count0 <= 0) {
      {
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              list<unsigned int>::nil();
        } else {
          _head = list<unsigned int>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int c = _loop_count0 - 1;
      {
        auto _cell = list<unsigned int>::cons(_loop_start, nullptr);
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        unsigned int _next_count0 = c;
        unsigned int _next_start = (_loop_start + 1);
        _loop_count0 = std::move(_next_count0);
        _loop_start = std::move(_next_start);
        continue;
      }
    }
  }
  return _head;
}

/// step_sum l sums with conditional contributions: even values as-is, odd
/// doubled.
__attribute__((pure)) unsigned int LoopifyLists::step_sum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        unsigned int contribution;
                        if ((2u ? _args.d_a0 % 2u : _args.d_a0) == 0u) {
                          contribution = _args.d_a0;
                        } else {
                          contribution = (_args.d_a0 * 2u);
                        }
                        _stack.emplace_back(_Call1{contribution});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// sum_abs l sums absolute values (using monus for nat).
__attribute__((pure)) unsigned int LoopifyLists::sum_abs(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
    const unsigned int base) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        unsigned int abs_val;
                        if (base <= _args.d_a0) {
                          abs_val = (((_args.d_a0 - base) > _args.d_a0
                                          ? 0
                                          : (_args.d_a0 - base)));
                        } else {
                          abs_val = (((base - _args.d_a0) > base
                                          ? 0
                                          : (base - _args.d_a0)));
                        }
                        _stack.emplace_back(_Call1{abs_val});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// four_elem l multi-case pattern matching on list structure.
__attribute__((pure)) unsigned int LoopifyLists::four_elem(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype((
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0 +
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
    decltype((
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0 +
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil &) -> void {
                                  _result = 1u;
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons &_args0) -> void {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename LoopifyLists::list<
                                              unsigned int>::Nil &) -> void {
                                            _result = 2u;
                                          },
                                          [&](const typename LoopifyLists::list<
                                              unsigned int>::Cons &_args1)
                                              -> void {
                                            std::visit(
                                                Overloaded{
                                                    [&](const typename LoopifyLists::
                                                            list<unsigned int>::
                                                                Nil &) -> void {
                                                      _result = 3u;
                                                    },
                                                    [&](const typename LoopifyLists::
                                                            list<unsigned int>::
                                                                Cons &_args2)
                                                        -> void {
                                                      _stack.emplace_back(
                                                          _Call1{
                                                              (_args.d_a0 +
                                                               _args0.d_a0),
                                                              (_args1.d_a0 +
                                                               _args2.d_a0)});
                                                      _stack.emplace_back(
                                                          _Enter{_args2.d_a1});
                                                    }},
                                                _args1.d_a1->v());
                                          }},
                                      _args0.d_a1->v());
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + (_f._s1 + _result)); }},
        _frame);
  }
  return _result;
}

/// between lo hi l filters elements in range lo, hi.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::between(
    const unsigned int lo, const unsigned int hi,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              if ((lo <= _args.d_a0 && _args.d_a0 <= hi)) {
                auto _cell = list<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

/// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
__attribute__((pure)) unsigned int LoopifyLists::categorize(
    const unsigned int k,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        unsigned int score;
                        if (k < _args.d_a0) {
                          score = 3u;
                        } else {
                          if (_args.d_a0 == k) {
                            score = 2u;
                          } else {
                            score = 1u;
                          }
                        }
                        _stack.emplace_back(_Call1{score});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// max_prefix_sum l maximum prefix sum (Kadane-like).
__attribute__((pure)) unsigned int LoopifyLists::max_prefix_sum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{_args});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int rest = _result;
              unsigned int sum = (_args.d_a0 + rest);
              if (0u <= sum) {
                _result = sum;
              } else {
                _result = 0u;
              }
            }},
        _frame);
  }
  return _result;
}

/// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::pairwise_sum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = list<unsigned int>::nil();
                        } else {
                          _head = list<unsigned int>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        auto _cell = list<unsigned int>::cons(
                            (_args.d_a0 + _args0.d_a0), nullptr);
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_l = _args0.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// weighted_sum i l weighted sum with increasing weights.
__attribute__((pure)) unsigned int LoopifyLists::weighted_sum(
    const unsigned int i,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int i;
  };

  struct _Call1 {
    decltype((
        std::declval<const unsigned int &>() *
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, i});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int i = _f.i;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{(i * _args.d_a0)});
                        _stack.emplace_back(_Enter{_args.d_a1, (i + 1)});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::prefix_sums(
    const unsigned int acc,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::cons(_loop_acc,
                                                     list<unsigned int>::nil());
              } else {
                _head = list<unsigned int>::cons(_loop_acc,
                                                 list<unsigned int>::nil());
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              auto _cell = list<unsigned int>::cons(_loop_acc, nullptr);
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                  _args.d_a1;
              unsigned int _next_acc = (_loop_acc + _args.d_a0);
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _head;
}

/// uniq_sorted l removes consecutive duplicates from sorted list.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::uniq_sorted(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = list<unsigned int>::cons(
                              _args.d_a0, list<unsigned int>::nil());
                        } else {
                          _head = list<unsigned int>::cons(
                              _args.d_a0, list<unsigned int>::nil());
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          _loop_l = _args.d_a1;
                        } else {
                          auto _cell =
                              list<unsigned int>::cons(_args.d_a0, nullptr);
                          if (_last) {
                            std::get<typename list<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          _loop_l = _args.d_a1;
                        }
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// Helper: take first n elements.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::take_n(
    const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              list<unsigned int>::nil();
        } else {
          _head = list<unsigned int>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int m = _loop_n - 1;
      std::visit(
          Overloaded{
              [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = list<unsigned int>::nil();
                } else {
                  _head = list<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename LoopifyLists::list<unsigned int>::Cons
                      &_args) {
                auto _cell = list<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                    _args.d_a1;
                unsigned int _next_n = m;
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

/// Helper: list length.
__attribute__((pure)) unsigned int LoopifyLists::len_list(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1) { _result = (_result + 1); }},
        _frame);
  }
  return _result;
}

/// windows n l returns all sliding windows of size n.
std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::windows_aux(
    const unsigned int fuel, const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<
      LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
      _head{};
  std::shared_ptr<
      LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
      _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename list<
              std::shared_ptr<LoopifyLists::list<unsigned int>>>::Cons>(
              _last->v_mut())
              .d_a1 =
              list<std::shared_ptr<LoopifyLists::list<unsigned int>>>::nil();
        } else {
          _head =
              list<std::shared_ptr<LoopifyLists::list<unsigned int>>>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename list<
                      std::shared_ptr<LoopifyLists::list<unsigned int>>>::Cons>(
                      _last->v_mut())
                      .d_a1 = list<
                      std::shared_ptr<LoopifyLists::list<unsigned int>>>::nil();
                } else {
                  _head = list<
                      std::shared_ptr<LoopifyLists::list<unsigned int>>>::nil();
                }
                _continue = false;
              },
              [&](const typename LoopifyLists::list<unsigned int>::Cons
                      &_args) {
                if (len_list(_loop_l) < n) {
                  if (_last) {
                    std::get<typename list<std::shared_ptr<
                        LoopifyLists::list<unsigned int>>>::Cons>(
                        _last->v_mut())
                        .d_a1 = list<std::shared_ptr<
                        LoopifyLists::list<unsigned int>>>::nil();
                  } else {
                    _head = list<std::shared_ptr<
                        LoopifyLists::list<unsigned int>>>::nil();
                  }
                  _continue = false;
                } else {
                  std::shared_ptr<LoopifyLists::list<unsigned int>> window =
                      take_n(n, _loop_l);
                  std::visit(
                      Overloaded{
                          [&](const typename LoopifyLists::list<
                              unsigned int>::Nil &) {
                            if (_last) {
                              std::get<typename list<std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = list<std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>>::nil();
                            } else {
                              _head = list<std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>>::nil();
                            }
                            _continue = false;
                          },
                          [&](const typename LoopifyLists::list<
                              unsigned int>::Cons &) {
                            auto _cell =
                                list<std::shared_ptr<LoopifyLists::list<
                                    unsigned int>>>::cons(window, nullptr);
                            if (_last) {
                              std::get<typename list<std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            std::shared_ptr<LoopifyLists::list<unsigned int>>
                                _next_l = _args.d_a1;
                            unsigned int _next_fuel = f;
                            _loop_l = std::move(_next_l);
                            _loop_fuel = std::move(_next_fuel);
                          }},
                      window->v());
                }
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::windows(
    const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  return windows_aux((len_list(l) + 1), n, l);
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool LoopifyLists::is_prefix_of(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l2) {
  bool _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              _result = true;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        _result = false;
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          std::shared_ptr<LoopifyLists::list<unsigned int>>
                              _next_l2 = _args0.d_a1;
                          std::shared_ptr<LoopifyLists::list<unsigned int>>
                              _next_l1 = _args.d_a1;
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

/// lookup_all key l finds all values for key in association list.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::lookup_all(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<
                std::pair<unsigned int, unsigned int>>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<
                std::pair<unsigned int, unsigned int>>::Cons &_args) {
              const unsigned int &k = _args.d_a0.first;
              const unsigned int &v = _args.d_a0.second;
              if (k == key) {
                auto _cell = list<unsigned int>::cons(v, nullptr);
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l = _args.d_a1;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

/// member x l checks if x is in the list.
__attribute__((pure)) bool LoopifyLists::member(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              _result = false;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              if (x == _args.d_a0) {
                _result = true;
                _continue = false;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _result;
}

/// product l multiplies all elements in the list.
__attribute__((pure)) unsigned int LoopifyLists::product(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 1u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{_args.d_a0});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 * _result); }},
        _frame);
  }
  return _result;
}

/// sum_list l sums all elements in the list.
__attribute__((pure)) unsigned int LoopifyLists::sum_list(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{_args.d_a0});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// flatten_nested l alternative flatten with different pattern: flattens one
/// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
/// :: flatten (xs :: rest).
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::flatten_nested_fuel(
    const unsigned int fuel,
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<
      LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
      _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        if (_last) {
          std::get<typename list<unsigned int>::Cons>(_last->v_mut()).d_a1 =
              list<unsigned int>::nil();
        } else {
          _head = list<unsigned int>::nil();
        }
        _continue = false;
      }
    } else {
      unsigned int f = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename LoopifyLists::list<
                  std::shared_ptr<LoopifyLists::list<unsigned int>>>::Nil &) {
                if (_last) {
                  std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = list<unsigned int>::nil();
                } else {
                  _head = list<unsigned int>::nil();
                }
                _continue = false;
              },
              [&](const typename LoopifyLists::list<std::shared_ptr<
                      LoopifyLists::list<unsigned int>>>::Cons &_args) {
                std::visit(
                    Overloaded{
                        [&](const typename LoopifyLists::list<unsigned int>::Nil
                                &) {
                          std::shared_ptr<LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>>
                              _next_l = _args.d_a1;
                          unsigned int _next_fuel = f;
                          _loop_l = std::move(_next_l);
                          _loop_fuel = std::move(_next_fuel);
                        },
                        [&](const typename LoopifyLists::list<
                            unsigned int>::Cons &_args0) {
                          auto _cell =
                              list<unsigned int>::cons(_args0.d_a0, nullptr);
                          if (_last) {
                            std::get<typename list<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          std::shared_ptr<LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>>
                              _next_l = list<std::shared_ptr<LoopifyLists::list<
                                  unsigned int>>>::cons(_args0.d_a1,
                                                        _args.d_a1);
                          unsigned int _next_fuel = f;
                          _loop_l = std::move(_next_l);
                          _loop_fuel = std::move(_next_fuel);
                        }},
                    _args.d_a0->v());
              }},
          _loop_l->v());
    }
  }
  return _head;
}

__attribute__((pure)) unsigned int LoopifyLists::sum_list_lengths(
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        l;
  };

  struct _Call1 {
    decltype(len_list(
        std::declval<const typename LoopifyLists::list<
            std::shared_ptr<LoopifyLists::list<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<
                  std::shared_ptr<LoopifyLists::list<unsigned int>>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Nil &)
                          -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{len_list(_args.d_a0)});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::flatten_nested(
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        &l) {
  return flatten_nested_fuel((sum_list_lengths(l) + 1), l);
}

/// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::compress(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = list<unsigned int>::cons(
                              _args.d_a0, list<unsigned int>::nil());
                        } else {
                          _head = list<unsigned int>::cons(
                              _args.d_a0, list<unsigned int>::nil());
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          _loop_l = _args.d_a1;
                        } else {
                          auto _cell =
                              list<unsigned int>::cons(_args.d_a0, nullptr);
                          if (_last) {
                            std::get<typename list<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          _loop_l = _args.d_a1;
                        }
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
/// (1,2),(3,4).
std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
LoopifyLists::group_pairs(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _head{};
  std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<
                    typename list<std::pair<unsigned int, unsigned int>>::Cons>(
                    _last->v_mut())
                    .d_a1 = list<std::pair<unsigned int, unsigned int>>::nil();
              } else {
                _head = list<std::pair<unsigned int, unsigned int>>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<
                              std::pair<unsigned int, unsigned int>>::Cons>(
                              _last->v_mut())
                              .d_a1 = list<
                              std::pair<unsigned int, unsigned int>>::nil();
                        } else {
                          _head = list<
                              std::pair<unsigned int, unsigned int>>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        auto _cell =
                            list<std::pair<unsigned int, unsigned int>>::cons(
                                std::make_pair(_args.d_a0, _args0.d_a0),
                                nullptr);
                        if (_last) {
                          std::get<typename list<
                              std::pair<unsigned int, unsigned int>>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell;
                        _loop_l = _args0.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
          std::shared_ptr<LoopifyLists::list<unsigned int>>>
LoopifyLists::swizzle(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
            std::shared_ptr<LoopifyLists::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void {
                        _result = std::make_pair(list<unsigned int>::nil(),
                                                 list<unsigned int>::nil());
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{_args});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> &odds =
                  _result.first;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> &evens =
                  _result.second;
              _result = std::make_pair(
                  list<unsigned int>::cons(_args.d_a0, evens), odds);
            }},
        _frame);
  }
  return _result;
}

/// index_of_aux x l i finds first index of x in l starting from i.
__attribute__((pure)) unsigned int LoopifyLists::index_of_aux(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
    const unsigned int i) {
  unsigned int _result;
  unsigned int _loop_i = i;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              _result = 0u;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              if (x == _args.d_a0) {
                _result = _loop_i;
                _continue = false;
              } else {
                unsigned int _next_i = (_loop_i + 1);
                std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                    _args.d_a1;
                _loop_i = std::move(_next_i);
                _loop_l = std::move(_next_l);
              }
            }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyLists::index_of(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  return index_of_aux(x, l, 0u);
}

/// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::interleave(std::shared_ptr<LoopifyLists::list<unsigned int>> l1,
                         std::shared_ptr<LoopifyLists::list<unsigned int>> l2) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = std::move(_loop_l2);
              } else {
                _head = std::move(_loop_l2);
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = std::move(_loop_l1);
                        } else {
                          _head = std::move(_loop_l1);
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        auto _cell =
                            list<unsigned int>::cons(_args.d_a0, nullptr);
                        auto _cell1 =
                            list<unsigned int>::cons(_args0.d_a0, nullptr);
                        std::get<typename list<unsigned int>::Cons>(
                            _cell->v_mut())
                            .d_a1 = _cell1;
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell1;
                        std::shared_ptr<LoopifyLists::list<unsigned int>>
                            _next_l2 = _args0.d_a1;
                        std::shared_ptr<LoopifyLists::list<unsigned int>>
                            _next_l1 = _args.d_a1;
                        _loop_l2 = std::move(_next_l2);
                        _loop_l1 = std::move(_next_l1);
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _head;
}

/// lookup key l finds value for key in association list.
__attribute__((pure)) unsigned int LoopifyLists::lookup(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>> &l) {
  unsigned int _result;
  std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename LoopifyLists::list<
                       std::pair<unsigned int, unsigned int>>::Nil &) {
                     _result = 0u;
                     _continue = false;
                   },
                   [&](const typename LoopifyLists::list<
                       std::pair<unsigned int, unsigned int>>::Cons &_args) {
                     const unsigned int &k = _args.d_a0.first;
                     const unsigned int &v = _args.d_a0.second;
                     if (k == key) {
                       _result = v;
                       _continue = false;
                     } else {
                       _loop_l = _args.d_a1;
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}

/// group l groups consecutive equal elements: 1,1,2,2,2,3 -> [1,1],[2,2,2],[3].
std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::group_fuel(
    const unsigned int fuel,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  struct _Call2 {
    decltype(list<unsigned int>::cons(
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0,
        list<unsigned int>::nil())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<
      LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = list<
                    std::shared_ptr<LoopifyLists::list<unsigned int>>>::nil();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename LoopifyLists::list<unsigned int>::Nil
                                &) -> void {
                          _result = list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::nil();
                        },
                        [&](const typename LoopifyLists::list<
                            unsigned int>::Cons &_args) -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyLists::list<
                                      unsigned int>::Nil &) -> void {
                                    _result = list<std::shared_ptr<
                                        LoopifyLists::list<unsigned int>>>::
                                        cons(list<unsigned int>::cons(
                                                 _args.d_a0,
                                                 list<unsigned int>::nil()),
                                             list<std::shared_ptr<
                                                 LoopifyLists::list<
                                                     unsigned int>>>::nil());
                                  },
                                  [&](const typename LoopifyLists::list<
                                      unsigned int>::Cons &_args0) -> void {
                                    if (_args.d_a0 == _args0.d_a0) {
                                      _stack.emplace_back(_Call1{_args});
                                      _stack.emplace_back(
                                          _Enter{_args.d_a1, f});
                                    } else {
                                      _stack.emplace_back(
                                          _Call2{list<unsigned int>::cons(
                                              _args.d_a0,
                                              list<unsigned int>::nil())});
                                      _stack.emplace_back(
                                          _Enter{_args.d_a1, f});
                                    }
                                  }},
                              _args.d_a1->v());
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Nil &)
                          -> void {
                        _result = list<
                            std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                            cons(list<unsigned int>::cons(
                                     _args.d_a0, list<unsigned int>::nil()),
                                 list<std::shared_ptr<
                                     LoopifyLists::list<unsigned int>>>::nil());
                      },
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Cons &_args1)
                          -> void {
                        _result = list<
                            std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                            cons(list<unsigned int>::cons(_args.d_a0,
                                                          _args1.d_a0),
                                 _args1.d_a1);
                      }},
                  _result->v());
            },
            [&](_Call2 _f) {
              _result =
                  list<std::shared_ptr<LoopifyLists::list<unsigned int>>>::cons(
                      _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::group(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  return group_fuel((len_list(l) + 1), l);
}

/// Internal helper: reverse a list.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::rev_helper(
    std::shared_ptr<LoopifyLists::list<unsigned int>> acc,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              _result = std::move(_loop_acc);
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                  _args.d_a1;
              std::shared_ptr<LoopifyLists::list<unsigned int>> _next_acc =
                  list<unsigned int>::cons(_args.d_a0, _loop_acc);
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _result;
}

/// reverse_insert x l inserts x and reverses at each step.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::reverse_insert(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(list<unsigned int>::nil()) _s0;
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void {
                        _result = list<unsigned int>::cons(
                            x, list<unsigned int>::nil());
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(
                            _Call1{list<unsigned int>::nil(), _args.d_a0});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result =
                  rev_helper(_f._s0, list<unsigned int>::cons(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

/// Internal helper: append lists.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::app_helper(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = std::move(l2);
              } else {
                _head = std::move(l2);
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              auto _cell = list<unsigned int>::cons(_args.d_a0, nullptr);
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = _cell;
              } else {
                _head = _cell;
              }
              _last = _cell;
              _loop_l1 = _args.d_a1;
            }},
        _loop_l1->v());
  }
  return _head;
}

/// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::double_append(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2;
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l1;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l1 =
                  _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = std::move(l2); },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{_args});
                        _stack.emplace_back(_Enter{std::move(l2), _args.d_a1});
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              std::shared_ptr<LoopifyLists::list<unsigned int>> rest = _result;
              _result =
                  list<unsigned int>::cons(_args.d_a0, app_helper(rest, rest));
            }},
        _frame);
  }
  return _result;
}

/// remove_if_sum_even l removes element if sum with next is even.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::remove_if_sum_even(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = list<unsigned int>::cons(
                              _args.d_a0, list<unsigned int>::nil());
                        } else {
                          _head = list<unsigned int>::cons(
                              _args.d_a0, list<unsigned int>::nil());
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        if ((2u ? (_args.d_a0 + _args0.d_a0) % 2u
                                : (_args.d_a0 + _args0.d_a0)) == 0u) {
                          _loop_l = _args.d_a1;
                        } else {
                          auto _cell =
                              list<unsigned int>::cons(_args.d_a0, nullptr);
                          if (_last) {
                            std::get<typename list<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          _loop_l = _args.d_a1;
                        }
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _head;
}

/// split_at n l splits list at index n into (prefix, suffix).
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
          std::shared_ptr<LoopifyLists::list<unsigned int>>>
LoopifyLists::split_at(const unsigned int n,
                       std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int n;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
            std::shared_ptr<LoopifyLists::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int n = _f.n;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void {
                        _result = std::make_pair(list<unsigned int>::nil(),
                                                 list<unsigned int>::nil());
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        if (n == 0u) {
                          _result = std::make_pair(list<unsigned int>::nil(),
                                                   std::move(l));
                        } else {
                          _stack.emplace_back(_Call1{_args});
                          _stack.emplace_back(_Enter{
                              _args.d_a1, (((n - 1u) > n ? 0 : (n - 1u)))});
                        }
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> &a =
                  _result.first;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> &b =
                  _result.second;
              _result =
                  std::make_pair(list<unsigned int>::cons(_args.d_a0, a), b);
            }},
        _frame);
  }
  return _result;
}

/// unzip l splits list of pairs into two lists.
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
          std::shared_ptr<LoopifyLists::list<unsigned int>>>
LoopifyLists::unzip(
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
        l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
            std::shared_ptr<LoopifyLists::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<
                          std::pair<unsigned int, unsigned int>>::Nil &)
                          -> void {
                        _result = std::make_pair(list<unsigned int>::nil(),
                                                 list<unsigned int>::nil());
                      },
                      [&](const typename LoopifyLists::list<
                          std::pair<unsigned int, unsigned int>>::Cons &_args)
                          -> void {
                        const unsigned int &a = _args.d_a0.first;
                        const unsigned int &b = _args.d_a0.second;
                        _stack.emplace_back(_Call1{b, a});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              unsigned int b = _f._s0;
              unsigned int a = _f._s1;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> &xs =
                  _result.first;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> &ys =
                  _result.second;
              _result = std::make_pair(list<unsigned int>::cons(a, xs),
                                       list<unsigned int>::cons(b, ys));
            }},
        _frame);
  }
  return _result;
}

/// nth n l default returns nth element or default if out of bounds.
__attribute__((pure)) unsigned int
LoopifyLists::nth(const unsigned int n,
                  const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
                  const unsigned int default0) {
  unsigned int _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              _result = default0;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              if (_loop_n == 0u) {
                _result = _args.d_a0;
                _continue = false;
              } else {
                std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                    _args.d_a1;
                unsigned int _next_n =
                    (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }
            }},
        _loop_l->v());
  }
  return _result;
}

/// last l default returns last element or default if empty.
__attribute__((pure)) unsigned int
LoopifyLists::last(const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
                   const unsigned int default0) {
  unsigned int _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              _result = default0;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        _result = _args.d_a0;
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &) { _loop_l = _args.d_a1; }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _result;
}

/// drop n l drops first n elements.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::drop(const unsigned int n,
                   std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_l.use_count() == 1 && _loop_l->v().index() == 0) {
      {
        _result = _loop_l;
        _continue = false;
      }
    } else {
      std::visit(
          Overloaded{
              [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
                _result = list<unsigned int>::nil();
                _continue = false;
              },
              [&](const typename LoopifyLists::list<unsigned int>::Cons
                      &_args) {
                if (_loop_n == 0u) {
                  _result = std::move(_loop_l);
                  _continue = false;
                } else {
                  std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                      _args.d_a1;
                  unsigned int _next_n =
                      (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                  _loop_l = std::move(_next_l);
                  _loop_n = std::move(_next_n);
                }
              }},
          _loop_l->v());
    }
  }
  return _result;
}

/// init l returns all but last element.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::init(const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _head{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = list<unsigned int>::nil();
              } else {
                _head = list<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = list<unsigned int>::nil();
                        } else {
                          _head = list<unsigned int>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &) {
                        auto _cell =
                            list<unsigned int>::cons(_args.d_a0, nullptr);
                        if (_last) {
                          std::get<typename list<unsigned int>::Cons>(
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

/// count x l counts occurrences of x in l.
__attribute__((pure)) unsigned int LoopifyLists::count(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        if (x == _args.d_a0) {
                          _stack.emplace_back(_Call1{});
                          _stack.emplace_back(_Enter{_args.d_a1});
                        } else {
                          _stack.emplace_back(_Enter{_args.d_a1});
                        }
                      }},
                  l->v());
            },
            [&](_Call1) { _result = (_result + 1); }},
        _frame);
  }
  return _result;
}

/// maximum l finds maximum element (returns 0 for empty list).
__attribute__((pure)) unsigned int LoopifyLists::maximum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = 0u; },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        std::visit(
                            Overloaded{[&](const typename LoopifyLists::list<
                                           unsigned int>::Nil &) -> void {
                                         _result = _args.d_a0;
                                       },
                                       [&](const typename LoopifyLists::list<
                                           unsigned int>::Cons &) -> void {
                                         _stack.emplace_back(_Call1{_args});
                                         _stack.emplace_back(
                                             _Enter{_args.d_a1});
                                       }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int max_rest = _result;
              if (max_rest <= _args.d_a0) {
                _result = _args.d_a0;
              } else {
                _result = max_rest;
              }
            }},
        _frame);
  }
  return _result;
}

/// minmax l finds both minimum and maximum in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::minmax(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = std::make_pair(0u, 0u); },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        std::visit(
                            Overloaded{[&](const typename LoopifyLists::list<
                                           unsigned int>::Nil &) -> void {
                                         _result = std::make_pair(_args.d_a0,
                                                                  _args.d_a0);
                                       },
                                       [&](const typename LoopifyLists::list<
                                           unsigned int>::Cons &) -> void {
                                         _stack.emplace_back(_Call1{_args});
                                         _stack.emplace_back(
                                             _Enter{_args.d_a1});
                                       }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              const unsigned int &lo = _result.first;
              const unsigned int &hi = _result.second;
              _result = std::make_pair(
                  [&]() -> unsigned int {
                    if (_args.d_a0 <= lo) {
                      return _args.d_a0;
                    } else {
                      return lo;
                    }
                  }(),
                  [&]() -> unsigned int {
                    if (hi <= _args.d_a0) {
                      return _args.d_a0;
                    } else {
                      return hi;
                    }
                  }());
            }},
        _frame);
  }
  return _result;
}

/// Helper for rotate_left.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::rotate_left_fuel(
    const unsigned int fuel, const unsigned int n,
    std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
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
      if (_loop_n == 0u) {
        {
          _result = std::move(_loop_l);
          _continue = false;
        }
      } else {
        if (_loop_l.use_count() == 1 && _loop_l->v().index() == 0) {
          {
            _result = _loop_l;
            _continue = false;
          }
        } else {
          std::visit(
              Overloaded{
                  [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
                    _result = list<unsigned int>::nil();
                    _continue = false;
                  },
                  [&](const typename LoopifyLists::list<unsigned int>::Cons
                          &_args) {
                    std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                        app_helper(_args.d_a1,
                                   list<unsigned int>::cons(
                                       _args.d_a0, list<unsigned int>::nil()));
                    unsigned int _next_n =
                        (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                    unsigned int _next_fuel = f;
                    _loop_l = std::move(_next_l);
                    _loop_n = std::move(_next_n);
                    _loop_fuel = std::move(_next_fuel);
                  }},
              _loop_l->v());
        }
      }
    }
  }
  return _result;
}

/// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
/// 3,4,1,2.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::rotate_left(
    const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  return rotate_left_fuel((n + 1), n, l);
}

/// intercalate sep lists joins lists with separator: intercalate 0 [1,2],[3,4]
/// -> 1,2,0,3,4.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::intercalate(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &sep,
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        &lists) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        lists;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyLists::list<
                 std::shared_ptr<LoopifyLists::list<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
    const std::shared_ptr<LoopifyLists::list<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{lists});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<
                  std::shared_ptr<LoopifyLists::list<unsigned int>>>>
                  lists = _f.lists;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Nil &)
                          -> void { _result = list<unsigned int>::nil(); },
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    std::shared_ptr<
                                        LoopifyLists::list<unsigned int>>>::Nil
                                        &) -> void { _result = _args.d_a0; },
                                [&](const typename LoopifyLists::list<
                                    std::shared_ptr<LoopifyLists::list<
                                        unsigned int>>>::Cons &) -> void {
                                  _stack.emplace_back(_Call1{_args.d_a0, sep});
                                  _stack.emplace_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  lists->v());
            },
            [&](_Call1 _f) {
              _result = app_helper(_f._s0, app_helper(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

/// majority l finds majority element using Boyer-Moore voting algorithm.
/// Returns (candidate, count).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::majority(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = std::make_pair(0u, 0u); },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil &) -> void {
                                  _result = std::make_pair(_args.d_a0, 1u);
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons &) -> void {
                                  _stack.emplace_back(_Call1{_args});
                                  _stack.emplace_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              const unsigned int &cand = _result.first;
              const unsigned int &cnt = _result.second;
              if (_args.d_a0 == cand) {
                _result = std::make_pair(cand, (cnt + 1));
              } else {
                if (cnt == 0u) {
                  _result = std::make_pair(_args.d_a0, 1u);
                } else {
                  _result = std::make_pair(
                      cand, (((cnt - 1u) > cnt ? 0 : (cnt - 1u))));
                }
              }
            }},
        _frame);
  }
  return _result;
}

/// zip3 l1 l2 l3 zips three lists into triples.
std::shared_ptr<LoopifyLists::list<
    std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
LoopifyLists::zip3(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l2,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l3) {
  std::shared_ptr<LoopifyLists::list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _head{};
  std::shared_ptr<LoopifyLists::list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _last{};
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l3 = l3;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename list<
                    std::pair<std::pair<unsigned int, unsigned int>,
                              unsigned int>>::Cons>(_last->v_mut())
                    .d_a1 =
                    list<std::pair<std::pair<unsigned int, unsigned int>,
                                   unsigned int>>::nil();
              } else {
                _head = list<std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int>>::nil();
              }
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) {
                        if (_last) {
                          std::get<typename list<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::Cons>(_last->v_mut())
                              .d_a1 = list<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                        } else {
                          _head = list<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args0) {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil &) {
                                  if (_last) {
                                    std::get<typename list<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::Cons>(_last->v_mut())
                                        .d_a1 = list<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                                  } else {
                                    _head = list<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                                  }
                                  _continue = false;
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons &_args1) {
                                  auto _cell = list<std::pair<
                                      std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::
                                      cons(std::make_pair(
                                               std::make_pair(_args.d_a0,
                                                              _args0.d_a0),
                                               _args1.d_a0),
                                           nullptr);
                                  if (_last) {
                                    std::get<typename list<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::Cons>(_last->v_mut())
                                        .d_a1 = _cell;
                                  } else {
                                    _head = _cell;
                                  }
                                  _last = _cell;
                                  std::shared_ptr<
                                      LoopifyLists::list<unsigned int>>
                                      _next_l3 = _args1.d_a1;
                                  std::shared_ptr<
                                      LoopifyLists::list<unsigned int>>
                                      _next_l2 = _args0.d_a1;
                                  std::shared_ptr<
                                      LoopifyLists::list<unsigned int>>
                                      _next_l1 = _args.d_a1;
                                  _loop_l3 = std::move(_next_l3);
                                  _loop_l2 = std::move(_next_l2);
                                  _loop_l1 = std::move(_next_l1);
                                }},
                            _loop_l3->v());
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _head;
}

/// sum_and_count l returns both sum and count in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::sum_and_count(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              &) -> void { _result = std::make_pair(0u, 0u); },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              &_args) -> void {
                        _stack.emplace_back(_Call1{_args});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              const unsigned int &s = _result.first;
              const unsigned int &c = _result.second;
              _result = std::make_pair((_args.d_a0 + s), (c + 1));
            }},
        _frame);
  }
  return _result;
}

/// elem_at n l returns element at index n (like nth but with different name).
__attribute__((pure)) std::optional<unsigned int> LoopifyLists::elem_at(
    const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil &) {
              _result = std::optional<unsigned int>();
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons &_args) {
              if (_loop_n == 0u) {
                _result = std::make_optional<unsigned int>(_args.d_a0);
                _continue = false;
              } else {
                std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                    _args.d_a1;
                unsigned int _next_n =
                    (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }
            }},
        _loop_l->v());
  }
  return _result;
}
