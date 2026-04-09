#include <loopify_sorting.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Consolidated UNIQUE sorting algorithms and related operations.
std::shared_ptr<List<unsigned int>>
LoopifySorting::insert(const unsigned int x,
                       std::shared_ptr<List<unsigned int>> l) {
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
                    .d_a1 =
                    List<unsigned int>::cons(x, List<unsigned int>::nil());
              } else {
                _head = List<unsigned int>::cons(x, List<unsigned int>::nil());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              if (x <= _args.d_a0) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = List<unsigned int>::cons(x, _loop_l);
                } else {
                  _head = List<unsigned int>::cons(x, _loop_l);
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
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::insertion_sort(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = insert(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::merge_fuel(const unsigned int fuel,
                           std::shared_ptr<List<unsigned int>> l1,
                           std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  unsigned int _loop_fuel = fuel;
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
                      .d_a1 = std::move(_loop_l2);
                } else {
                  _head = std::move(_loop_l2);
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
                                .d_a1 = std::move(_loop_l1);
                          } else {
                            _head = std::move(_loop_l1);
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons _args0) {
                          if (_args.d_a0 <= _args0.d_a0) {
                            auto _cell =
                                List<unsigned int>::cons(_args.d_a0, nullptr);
                            if (_last) {
                              std::get<typename List<unsigned int>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            std::shared_ptr<List<unsigned int>> _next_l1 =
                                _args.d_a1;
                            unsigned int _next_fuel = f;
                            _loop_l1 = std::move(_next_l1);
                            _loop_fuel = std::move(_next_fuel);
                          } else {
                            auto _cell =
                                List<unsigned int>::cons(_args0.d_a0, nullptr);
                            if (_last) {
                              std::get<typename List<unsigned int>::Cons>(
                                  _last->v_mut())
                                  .d_a1 = _cell;
                            } else {
                              _head = _cell;
                            }
                            _last = _cell;
                            std::shared_ptr<List<unsigned int>> _next_l2 =
                                _args0.d_a1;
                            unsigned int _next_fuel = f;
                            _loop_l2 = std::move(_next_l2);
                            _loop_fuel = std::move(_next_fuel);
                          }
                        }},
                    _loop_l2->v());
              }},
          _loop_l1->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::merge(const std::shared_ptr<List<unsigned int>> &l1,
                      const std::shared_ptr<List<unsigned int>> &l2) {
  return merge_fuel((len_impl<unsigned int>(l1) + len_impl<unsigned int>(l2)),
                    l1, l2);
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::merge_sort_fuel(const unsigned int fuel,
                                std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    unsigned int _s1;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = std::move(l);
              } else {
                unsigned int f = fuel - 1;
                if (l.use_count() == 1 && l->v().index() == 0) {
                  auto &_rf = std::get<0>(l->v_mut());
                  _result = l;
                } else {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil _args)
                              -> void { _result = List<unsigned int>::nil(); },
                          [&](const typename List<unsigned int>::Cons _args)
                              -> void {
                            std::visit(
                                Overloaded{
                                    [&](const typename List<unsigned int>::Nil
                                            _args0) -> void {
                                      _result = std::move(l);
                                    },
                                    [&](const typename List<unsigned int>::Cons
                                            _args0) -> void {
                                      std::shared_ptr<List<unsigned int>> l1 =
                                          split<unsigned int>(l).first;
                                      std::shared_ptr<List<unsigned int>> l2 =
                                          split<unsigned int>(l).second;
                                      _stack.push_back(_Call1{l1, f});
                                      _stack.push_back(_Enter{l2, f});
                                    }},
                                _args.d_a1->v());
                          }},
                      l->v());
                }
              }
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) { _result = merge(_result, _f._s0); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::merge_sort(const std::shared_ptr<List<unsigned int>> &l) {
  return merge_sort_fuel(len_impl<unsigned int>(l), l);
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifySorting::partition(const unsigned int pivot,
                          const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const unsigned int _s0;
    const typename List<unsigned int>::Cons _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
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
                                 -> void {
                               _result =
                                   std::make_pair(List<unsigned int>::nil(),
                                                  List<unsigned int>::nil());
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{pivot, _args});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     const unsigned int pivot = _f._s0;
                     const typename List<unsigned int>::Cons _args = _f._s1;
                     std::shared_ptr<List<unsigned int>> lo = _result.first;
                     std::shared_ptr<List<unsigned int>> hi = _result.second;
                     if (_args.d_a0 <= pivot) {
                       _result = std::make_pair(
                           List<unsigned int>::cons(_args.d_a0, lo), hi);
                     } else {
                       _result = std::make_pair(
                           lo, List<unsigned int>::cons(_args.d_a0, hi));
                     }
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::quicksort_fuel(const unsigned int fuel,
                               std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
    unsigned int _s1;
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s2;
  };

  struct _Call2 {
    std::shared_ptr<List<unsigned int>> _s0;
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = std::move(l);
              } else {
                unsigned int f = fuel - 1;
                if (l.use_count() == 1 && l->v().index() == 0) {
                  auto &_rf = std::get<0>(l->v_mut());
                  _result = l;
                } else {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil _args)
                              -> void { _result = List<unsigned int>::nil(); },
                          [&](const typename List<unsigned int>::Cons _args)
                              -> void {
                            std::shared_ptr<List<unsigned int>> lo =
                                partition(_args.d_a0, _args.d_a1).first;
                            std::shared_ptr<List<unsigned int>> hi =
                                partition(_args.d_a0, _args.d_a1).second;
                            _stack.push_back(_Call1{lo, f, _args.d_a0});
                            _stack.push_back(_Enter{hi, f});
                          }},
                      l->v());
                }
              }
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s2});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) {
              _result = _result->app(List<unsigned int>::cons(_f._s1, _f._s0));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::quicksort(const std::shared_ptr<List<unsigned int>> &l) {
  return quicksort_fuel(len_impl<unsigned int>(l), l);
}

__attribute__((pure)) bool
LoopifySorting::is_sorted_aux(const unsigned int prev,
                              const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_prev = prev;
  bool _continue = true;
  while (_continue) {
    std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                            _result = true;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons _args) {
                            if (_loop_prev <= _args.d_a0) {
                              std::shared_ptr<List<unsigned int>> _next_l =
                                  _args.d_a1;
                              unsigned int _next_prev = _args.d_a0;
                              _loop_l = std::move(_next_l);
                              _loop_prev = std::move(_next_prev);
                            } else {
                              _result = false;
                              _continue = false;
                            }
                          }},
               _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) bool
LoopifySorting::is_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil _args) -> bool {
                   return true;
                 },
                 [](const typename List<unsigned int>::Cons _args) -> bool {
                   return is_sorted_aux(_args.d_a0, _args.d_a1);
                 }},
      l->v());
}

/// remove_duplicates removes consecutive duplicates from sorted list.
std::shared_ptr<List<unsigned int>> LoopifySorting::remove_duplicates(
    const std::shared_ptr<List<unsigned int>> &l) {
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
                              .d_a1 = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        } else {
                          _head = List<unsigned int>::cons(
                              _args.d_a0, List<unsigned int>::nil());
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          _loop_l = _args.d_a1;
                        } else {
                          auto _cell =
                              List<unsigned int>::cons(_args.d_a0, nullptr);
                          if (_last) {
                            std::get<typename List<unsigned int>::Cons>(
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

/// uniq_sorted variant that preserves order.
std::shared_ptr<List<unsigned int>>
LoopifySorting::uniq_sorted_aux(const unsigned int prev, const bool seen,
                                const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _loop_seen = seen;
  unsigned int _loop_prev = prev;
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
              if (_loop_seen) {
                if (_loop_prev == _args.d_a0) {
                  std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                  bool _next_seen = true;
                  unsigned int _next_prev = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_seen = std::move(_next_seen);
                  _loop_prev = std::move(_next_prev);
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
                  bool _next_seen = true;
                  unsigned int _next_prev = _args.d_a0;
                  _loop_l = std::move(_next_l);
                  _loop_seen = std::move(_next_seen);
                  _loop_prev = std::move(_next_prev);
                }
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
                bool _next_seen = true;
                unsigned int _next_prev = _args.d_a0;
                _loop_l = std::move(_next_l);
                _loop_seen = std::move(_next_seen);
                _loop_prev = std::move(_next_prev);
              }
            }},
        _loop_l->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifySorting::uniq_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  return uniq_sorted_aux(0u, false, l);
}
