#include <loopify_list_relations.h>

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

__attribute__((pure)) bool LoopifyListRelations::is_prefix_of(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>().d_a0 ==
             std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) -> void {
                        _result = true;
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &)
                                    -> void { _result = false; },
                                [&](const typename List<unsigned int>::Cons
                                        &_args0) -> void {
                                  _stack.emplace_back(
                                      _Call1{_args.d_a0 == _args0.d_a0});
                                  _stack.emplace_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                }},
                            l2->v());
                      }},
                  l1->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 && _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyListRelations::is_suffix_of(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  if (len2 < len1) {
    return false;
  } else {
    unsigned int diff = (((len2 - len1) > len2 ? 0 : (len2 - len1)));
    std::shared_ptr<List<unsigned int>> suffix;
    std::function<std::shared_ptr<List<unsigned int>>(
        unsigned int, std::shared_ptr<List<unsigned int>>)>
        drop;
    drop = [](unsigned int n, std::shared_ptr<List<unsigned int>> xs)
        -> std::shared_ptr<List<unsigned int>> {
      std::shared_ptr<List<unsigned int>> _result;
      std::shared_ptr<List<unsigned int>> _loop_xs = xs;
      unsigned int _loop_n = n;
      bool _continue = true;
      while (_continue) {
        if (_loop_n <= 0) {
          {
            _result = _loop_xs;
            _continue = false;
          }
        } else {
          unsigned int n_ = _loop_n - 1;
          if (_loop_xs.use_count() == 1 && _loop_xs->v().index() == 0) {
            {
              _result = _loop_xs;
              _continue = false;
            }
          } else {
            std::visit(
                Overloaded{[&](const typename List<unsigned int>::Nil &) {
                             _result = List<unsigned int>::nil();
                             _continue = false;
                           },
                           [&](const typename List<unsigned int>::Cons &_args) {
                             std::shared_ptr<List<unsigned int>> _next_xs =
                                 _args.d_a1;
                             unsigned int _next_n = n_;
                             _loop_xs = std::move(_next_xs);
                             _loop_n = std::move(_next_n);
                           }},
                _loop_xs->v());
          }
        }
      }
      return _result;
    };
    suffix = drop(diff, l2);
    std::function<bool(std::shared_ptr<List<unsigned int>>,
                       std::shared_ptr<List<unsigned int>>)>
        eq;
    eq = [](std::shared_ptr<List<unsigned int>> a,
            std::shared_ptr<List<unsigned int>> b) -> bool {
      bool _result;
      std::shared_ptr<List<unsigned int>> _loop_b = b;
      std::shared_ptr<List<unsigned int>> _loop_a = a;
      bool _continue = true;
      while (_continue) {
        std::visit(
            Overloaded{
                [&](const typename List<unsigned int>::Nil &) {
                  _result = std::visit(
                      Overloaded{[](const typename List<unsigned int>::Nil &)
                                     -> bool { return true; },
                                 [](const typename List<unsigned int>::Cons &)
                                     -> bool { return false; }},
                      _loop_b->v());
                  _continue = false;
                },
                [&](const typename List<unsigned int>::Cons &_args0) {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil &) {
                            _result = false;
                            _continue = false;
                          },
                          [&](const typename List<unsigned int>::Cons &_args1) {
                            if (_args0.d_a0 == _args1.d_a0) {
                              std::shared_ptr<List<unsigned int>> _next_b =
                                  _args1.d_a1;
                              std::shared_ptr<List<unsigned int>> _next_a =
                                  _args0.d_a1;
                              _loop_b = std::move(_next_b);
                              _loop_a = std::move(_next_a);
                            } else {
                              _result = false;
                              _continue = false;
                            }
                          }},
                      _loop_b->v());
                }},
            _loop_a->v());
      }
      return _result;
    };
    return eq(l1, suffix);
  }
}

__attribute__((pure)) bool LoopifyListRelations::is_infix_of_aux(
    const std::shared_ptr<List<unsigned int>> &needle,
    const std::shared_ptr<List<unsigned int>> &haystack) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_haystack = haystack;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              _result = std::visit(
                  Overloaded{
                      [](const typename List<unsigned int>::Nil &) -> bool {
                        return true;
                      },
                      [](const typename List<unsigned int>::Cons &) -> bool {
                        return false;
                      }},
                  needle->v());
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if (is_prefix_of(needle, _loop_haystack)) {
                _result = true;
                _continue = false;
              } else {
                _loop_haystack = _args.d_a1;
              }
            }},
        _loop_haystack->v());
  }
  return _result;
}

__attribute__((pure)) bool LoopifyListRelations::is_infix_of(
    const std::shared_ptr<List<unsigned int>> &_x0,
    const std::shared_ptr<List<unsigned int>> &_x1) {
  return is_infix_of_aux(_x0, _x1);
}

std::shared_ptr<List<unsigned int>> LoopifyListRelations::find_sublists_aux(
    const std::shared_ptr<List<unsigned int>> &needle,
    const std::shared_ptr<List<unsigned int>> &haystack,
    const unsigned int idx) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  unsigned int _loop_idx = idx;
  std::shared_ptr<List<unsigned int>> _loop_haystack = haystack;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if (is_prefix_of(needle, _loop_haystack)) {
                auto _cell = List<unsigned int>::cons(_loop_idx, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                unsigned int _next_idx = (_loop_idx + 1u);
                std::shared_ptr<List<unsigned int>> _next_haystack = _args.d_a1;
                _loop_idx = std::move(_next_idx);
                _loop_haystack = std::move(_next_haystack);
              } else {
                unsigned int _next_idx = (_loop_idx + 1u);
                std::shared_ptr<List<unsigned int>> _next_haystack = _args.d_a1;
                _loop_idx = std::move(_next_idx);
                _loop_haystack = std::move(_next_haystack);
              }
            }},
        _loop_haystack->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListRelations::find_sublists(
    const std::shared_ptr<List<unsigned int>> &needle,
    const std::shared_ptr<List<unsigned int>> &haystack) {
  return find_sublists_aux(needle, haystack, 0u);
}

__attribute__((pure)) bool
LoopifyListRelations::list_eq(const std::shared_ptr<List<unsigned int>> &l1,
                              const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>().d_a0 ==
             std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) -> void {
                        _result = std::visit(
                            Overloaded{
                                [](const typename List<unsigned int>::Nil &)
                                    -> bool { return true; },
                                [](const typename List<unsigned int>::Cons &)
                                    -> bool { return false; }},
                            l2->v());
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &)
                                    -> void { _result = false; },
                                [&](const typename List<unsigned int>::Cons
                                        &_args0) -> void {
                                  _stack.emplace_back(
                                      _Call1{_args.d_a0 == _args0.d_a0});
                                  _stack.emplace_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                }},
                            l2->v());
                      }},
                  l1->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 && _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListRelations::list_compare(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              _result = std::visit(
                  Overloaded{[](const typename List<unsigned int>::Nil &)
                                 -> unsigned int { return 0u; },
                             [](const typename List<unsigned int>::Cons &)
                                 -> unsigned int { return 1u; }},
                  _loop_l2->v());
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        _result = 2u;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        if (_args.d_a0 < _args0.d_a0) {
                          _result = 1u;
                          _continue = false;
                        } else {
                          if (_args0.d_a0 < _args.d_a0) {
                            _result = 2u;
                            _continue = false;
                          } else {
                            std::shared_ptr<List<unsigned int>> _next_l2 =
                                _args0.d_a1;
                            std::shared_ptr<List<unsigned int>> _next_l1 =
                                _args.d_a1;
                            _loop_l2 = std::move(_next_l2);
                            _loop_l1 = std::move(_next_l1);
                          }
                        }
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListRelations::zip(const std::shared_ptr<List<unsigned int>> &l1,
                          const std::shared_ptr<List<unsigned int>> &l2) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
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
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
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
                      [&](const typename List<unsigned int>::Cons &_args0) {
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
                        std::shared_ptr<List<unsigned int>> _next_l2 =
                            _args0.d_a1;
                        std::shared_ptr<List<unsigned int>> _next_l1 =
                            _args.d_a1;
                        _loop_l2 = std::move(_next_l2);
                        _loop_l1 = std::move(_next_l1);
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _head;
}

std::shared_ptr<
    List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
LoopifyListRelations::zip3(const std::shared_ptr<List<unsigned int>> &l1,
                           const std::shared_ptr<List<unsigned int>> &l2,
                           const std::shared_ptr<List<unsigned int>> &l3) {
  std::shared_ptr<
      List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _head{};
  std::shared_ptr<
      List<std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _last{};
  std::shared_ptr<List<unsigned int>> _loop_l3 = l3;
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<
                    std::pair<std::pair<unsigned int, unsigned int>,
                              unsigned int>>::Cons>(_last->v_mut())
                    .d_a1 =
                    List<std::pair<std::pair<unsigned int, unsigned int>,
                                   unsigned int>>::nil();
              } else {
                _head = List<std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int>>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        if (_last) {
                          std::get<typename List<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::Cons>(_last->v_mut())
                              .d_a1 = List<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                        } else {
                          _head = List<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &) {
                                  if (_last) {
                                    std::get<typename List<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::Cons>(_last->v_mut())
                                        .d_a1 = List<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                                  } else {
                                    _head = List<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::nil();
                                  }
                                  _continue = false;
                                },
                                [&](const typename List<unsigned int>::Cons
                                        &_args1) {
                                  auto _cell = List<std::pair<
                                      std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::
                                      cons(std::make_pair(
                                               std::make_pair(_args.d_a0,
                                                              _args0.d_a0),
                                               _args1.d_a0),
                                           nullptr);
                                  if (_last) {
                                    std::get<typename List<std::pair<
                                        std::pair<unsigned int, unsigned int>,
                                        unsigned int>>::Cons>(_last->v_mut())
                                        .d_a1 = _cell;
                                  } else {
                                    _head = _cell;
                                  }
                                  _last = _cell;
                                  std::shared_ptr<List<unsigned int>> _next_l3 =
                                      _args1.d_a1;
                                  std::shared_ptr<List<unsigned int>> _next_l2 =
                                      _args0.d_a1;
                                  std::shared_ptr<List<unsigned int>> _next_l1 =
                                      _args.d_a1;
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

std::shared_ptr<List<unsigned int>>
LoopifyListRelations::interleave(std::shared_ptr<List<unsigned int>> l1,
                                 std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = std::move(_loop_l2);
              } else {
                _head = std::move(_loop_l2);
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) {
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = std::move(_loop_l1);
                        } else {
                          _head = std::move(_loop_l1);
                        }
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons &_args0) {
                        auto _cell =
                            List<unsigned int>::cons(_args.d_a0, nullptr);
                        auto _cell1 =
                            List<unsigned int>::cons(_args0.d_a0, nullptr);
                        std::get<typename List<unsigned int>::Cons>(
                            _cell->v_mut())
                            .d_a1 = _cell1;
                        if (_last) {
                          std::get<typename List<unsigned int>::Cons>(
                              _last->v_mut())
                              .d_a1 = _cell;
                        } else {
                          _head = _cell;
                        }
                        _last = _cell1;
                        std::shared_ptr<List<unsigned int>> _next_l2 =
                            _args0.d_a1;
                        std::shared_ptr<List<unsigned int>> _next_l1 =
                            _args.d_a1;
                        _loop_l2 = std::move(_next_l2);
                        _loop_l1 = std::move(_next_l1);
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListRelations::merge_fuel(const unsigned int fuel,
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
      unsigned int fuel_ = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = std::move(_loop_l2);
                } else {
                  _head = std::move(_loop_l2);
                }
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons &_args) {
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil &) {
                          if (_last) {
                            std::get<typename List<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = std::move(_loop_l1);
                          } else {
                            _head = std::move(_loop_l1);
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons &_args0) {
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
                            unsigned int _next_fuel = fuel_;
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
                            unsigned int _next_fuel = fuel_;
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
LoopifyListRelations::merge(const std::shared_ptr<List<unsigned int>> &l1,
                            const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  return merge_fuel((len1 + len2), l1, l2);
}

std::shared_ptr<List<unsigned int>>
LoopifyListRelations::union_(const std::shared_ptr<List<unsigned int>> &l1,
                             std::shared_ptr<List<unsigned int>> l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = std::move(_loop_l2);
              } else {
                _head = std::move(_loop_l2);
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if ([&]() {
                    std::function<bool(unsigned int,
                                       std::shared_ptr<List<unsigned int>>)>
                        member;
                    member =
                        [&](unsigned int y,
                            std::shared_ptr<List<unsigned int>> ys) -> bool {
                      struct _Enter {
                        std::shared_ptr<List<unsigned int>> ys;
                      };
                      struct _Call1 {
                        decltype(std::declval<unsigned int &>() ==
                                 std::declval<const typename List<
                                     unsigned int>::Cons &>()
                                     .d_a0) _s0;
                      };
                      using _Frame = std::variant<_Enter, _Call1>;
                      bool _result{};
                      std::vector<_Frame> _stack;
                      _stack.emplace_back(_Enter{ys});
                      while (!_stack.empty()) {
                        _Frame _frame = std::move(_stack.back());
                        _stack.pop_back();
                        std::visit(
                            Overloaded{
                                [&](_Enter _f) {
                                  std::shared_ptr<List<unsigned int>> ys =
                                      _f.ys;
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              unsigned int>::Nil &) -> void {
                                            _result = false;
                                          },
                                          [&](const typename List<
                                              unsigned int>::Cons &_args)
                                              -> void {
                                            _stack.emplace_back(
                                                _Call1{y == _args.d_a0});
                                            _stack.emplace_back(
                                                _Enter{_args.d_a1});
                                          }},
                                      ys->v());
                                },
                                [&](_Call1 _f) {
                                  _result = (_f._s0 || _result);
                                }},
                            _frame);
                      }
                      return _result;
                    };
                    return member(_args.d_a0, _loop_l2);
                  }()) {
                std::shared_ptr<List<unsigned int>> _next_l2 =
                    std::move(_loop_l2);
                std::shared_ptr<List<unsigned int>> _next_l1 = _args.d_a1;
                _loop_l2 = std::move(_next_l2);
                _loop_l1 = std::move(_next_l1);
              } else {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l1 = _args.d_a1;
              }
            }},
        _loop_l1->v());
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListRelations::intersection(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::nil();
              } else {
                _head = List<unsigned int>::nil();
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
              if ([&]() {
                    std::function<bool(unsigned int,
                                       std::shared_ptr<List<unsigned int>>)>
                        member;
                    member =
                        [&](unsigned int y,
                            std::shared_ptr<List<unsigned int>> ys) -> bool {
                      struct _Enter {
                        std::shared_ptr<List<unsigned int>> ys;
                      };
                      struct _Call1 {
                        decltype(std::declval<unsigned int &>() ==
                                 std::declval<const typename List<
                                     unsigned int>::Cons &>()
                                     .d_a0) _s0;
                      };
                      using _Frame = std::variant<_Enter, _Call1>;
                      bool _result{};
                      std::vector<_Frame> _stack;
                      _stack.emplace_back(_Enter{ys});
                      while (!_stack.empty()) {
                        _Frame _frame = std::move(_stack.back());
                        _stack.pop_back();
                        std::visit(
                            Overloaded{
                                [&](_Enter _f) {
                                  std::shared_ptr<List<unsigned int>> ys =
                                      _f.ys;
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              unsigned int>::Nil &) -> void {
                                            _result = false;
                                          },
                                          [&](const typename List<
                                              unsigned int>::Cons &_args)
                                              -> void {
                                            _stack.emplace_back(
                                                _Call1{y == _args.d_a0});
                                            _stack.emplace_back(
                                                _Enter{_args.d_a1});
                                          }},
                                      ys->v());
                                },
                                [&](_Call1 _f) {
                                  _result = (_f._s0 || _result);
                                }},
                            _frame);
                      }
                      return _result;
                    };
                    return member(_args.d_a0, l2);
                  }()) {
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                _loop_l1 = _args.d_a1;
              } else {
                _loop_l1 = _args.d_a1;
              }
            }},
        _loop_l1->v());
  }
  return _head;
}
