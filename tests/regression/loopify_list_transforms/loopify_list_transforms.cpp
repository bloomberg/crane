#include <loopify_list_transforms.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::run_length_encode(
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
  _stack.emplace_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil &) -> void {
                        _result =
                            List<std::pair<unsigned int, unsigned int>>::nil();
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &)
                                    -> void {
                                  _result = List<
                                      std::pair<unsigned int, unsigned int>>::
                                      cons(
                                          std::make_pair(_args.d_a0, 1u),
                                          List<std::pair<unsigned int,
                                                         unsigned int>>::nil());
                                },
                                [&](const typename List<unsigned int>::Cons &)
                                    -> void {
                                  _stack.emplace_back(_Call1{_args});
                                  _stack.emplace_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Nil &)
                          -> void {
                        _result =
                            List<std::pair<unsigned int, unsigned int>>::cons(
                                std::make_pair(_args.d_a0, 1u),
                                List<std::pair<unsigned int,
                                               unsigned int>>::nil());
                      },
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Cons &_args1)
                          -> void {
                        const unsigned int &y = _args1.d_a0.first;
                        const unsigned int &n = _args1.d_a0.second;
                        if (_args.d_a0 == y) {
                          _result =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(y, (n + 1u)), _args1.d_a1);
                        } else {
                          _result =
                              List<std::pair<unsigned int, unsigned int>>::cons(
                                  std::make_pair(_args.d_a0, 1u),
                                  List<std::pair<unsigned int, unsigned int>>::
                                      cons(std::make_pair(y, n), _args1.d_a1));
                        }
                      }},
                  _result->v());
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::prefix_sums(
    const unsigned int acc, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil &) {
              if (_last) {
                std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                    .d_a1 = List<unsigned int>::cons(_loop_acc,
                                                     List<unsigned int>::nil());
              } else {
                _head = List<unsigned int>::cons(_loop_acc,
                                                 List<unsigned int>::nil());
              }
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons &_args) {
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

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::sliding_pairs_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _head{};
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
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
      unsigned int fuel_ = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil &) {
                if (_last) {
                  std::get<typename List<
                      std::pair<unsigned int, unsigned int>>::Cons>(
                      _last->v_mut())
                      .d_a1 =
                      List<std::pair<unsigned int, unsigned int>>::nil();
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
                          std::shared_ptr<List<unsigned int>> _next_l =
                              _args.d_a1;
                          unsigned int _next_fuel = fuel_;
                          _loop_l = std::move(_next_l);
                          _loop_fuel = std::move(_next_fuel);
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::sliding_pairs(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return sliding_pairs_fuel(len, l);
}

__attribute__((pure)) unsigned int
LoopifyListTransforms::abs_diff(const unsigned int x, const unsigned int y) {
  if (y < x) {
    return (((x - y) > x ? 0 : (x - y)));
  } else {
    return (((y - x) > y ? 0 : (y - x)));
  }
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::differences_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
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
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
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
                                .d_a1 = List<unsigned int>::nil();
                          } else {
                            _head = List<unsigned int>::nil();
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons &_args0) {
                          auto _cell = List<unsigned int>::cons(
                              abs_diff(_args.d_a0, _args0.d_a0), nullptr);
                          if (_last) {
                            std::get<typename List<unsigned int>::Cons>(
                                _last->v_mut())
                                .d_a1 = _cell;
                          } else {
                            _head = _cell;
                          }
                          _last = _cell;
                          std::shared_ptr<List<unsigned int>> _next_l =
                              _args.d_a1;
                          unsigned int _next_fuel = fuel_;
                          _loop_l = std::move(_next_l);
                          _loop_fuel = std::move(_next_fuel);
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::differences(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return differences_fuel(len, l);
}

std::shared_ptr<List<unsigned int>>
LoopifyListTransforms::take(const unsigned int n,
                            const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<unsigned int>> _head{};
  std::shared_ptr<List<unsigned int>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
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
      unsigned int n_ = _loop_n - 1;
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
                auto _cell = List<unsigned int>::cons(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<unsigned int>::Cons>(_last->v_mut())
                      .d_a1 = _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
                unsigned int _next_n = n_;
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>>
LoopifyListTransforms::drop(const unsigned int n,
                            std::shared_ptr<List<unsigned int>> l) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        _result = std::move(_loop_l);
        _continue = false;
      }
    } else {
      unsigned int n_ = _loop_n - 1;
      if (_loop_l.use_count() == 1 && _loop_l->v().index() == 0) {
        {
          _result = _loop_l;
          _continue = false;
        }
      } else {
        std::visit(
            Overloaded{[&](const typename List<unsigned int>::Nil &) {
                         _result = List<unsigned int>::nil();
                         _continue = false;
                       },
                       [&](const typename List<unsigned int>::Cons &_args) {
                         std::shared_ptr<List<unsigned int>> _next_l =
                             _args.d_a1;
                         unsigned int _next_n = n_;
                         _loop_l = std::move(_next_l);
                         _loop_n = std::move(_next_n);
                       }},
            _loop_l->v());
      }
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListTransforms::chunks_of_fuel(
    const unsigned int fuel, const unsigned int n,
    const std::shared_ptr<List<unsigned int>> &l) {
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _head{};
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _last{};
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
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
      unsigned int fuel_ = _loop_fuel - 1;
      if (n <= 0u) {
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
        std::visit(
            Overloaded{[&](const typename List<unsigned int>::Nil &) {
                         if (_last) {
                           std::get<typename List<
                               std::shared_ptr<List<unsigned int>>>::Cons>(
                               _last->v_mut())
                               .d_a1 =
                               List<std::shared_ptr<List<unsigned int>>>::nil();
                         } else {
                           _head =
                               List<std::shared_ptr<List<unsigned int>>>::nil();
                         }
                         _continue = false;
                       },
                       [&](const typename List<unsigned int>::Cons &) {
                         auto _cell =
                             List<std::shared_ptr<List<unsigned int>>>::cons(
                                 take(n, _loop_l), nullptr);
                         if (_last) {
                           std::get<typename List<
                               std::shared_ptr<List<unsigned int>>>::Cons>(
                               _last->v_mut())
                               .d_a1 = _cell;
                         } else {
                           _head = _cell;
                         }
                         _last = _cell;
                         std::shared_ptr<List<unsigned int>> _next_l =
                             drop(n, _loop_l);
                         unsigned int _next_fuel = fuel_;
                         _loop_l = std::move(_next_l);
                         _loop_fuel = std::move(_next_fuel);
                       }},
            _loop_l->v());
      }
    }
  }
  return _head;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListTransforms::chunks_of(const unsigned int n,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return chunks_of_fuel(len, n, l);
}

std::shared_ptr<List<unsigned int>>
LoopifyListTransforms::rotate_left_fuel(const unsigned int fuel,
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
      unsigned int fuel_ = _loop_fuel - 1;
      if (_loop_n <= 0u) {
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
              Overloaded{[&](const typename List<unsigned int>::Nil &) {
                           _result = List<unsigned int>::nil();
                           _continue = false;
                         },
                         [&](const typename List<unsigned int>::Cons &_args) {
                           std::shared_ptr<List<unsigned int>> rotated =
                               _args.d_a1->app(List<unsigned int>::cons(
                                   _args.d_a0, List<unsigned int>::nil()));
                           std::shared_ptr<List<unsigned int>> _next_l =
                               std::move(rotated);
                           unsigned int _next_n = ((
                               (_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                           unsigned int _next_fuel = fuel_;
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

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::rotate_left(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  return rotate_left_fuel((n + 1u), n, l);
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::uniq_sorted_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
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
                      .d_a1 = List<unsigned int>::nil();
                } else {
                  _head = List<unsigned int>::nil();
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
                                .d_a1 = List<unsigned int>::cons(
                                _args.d_a0, List<unsigned int>::nil());
                          } else {
                            _head = List<unsigned int>::cons(
                                _args.d_a0, List<unsigned int>::nil());
                          }
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons &_args0) {
                          if (_args.d_a0 == _args0.d_a0) {
                            std::shared_ptr<List<unsigned int>> _next_l =
                                _args.d_a1;
                            unsigned int _next_fuel = fuel_;
                            _loop_l = std::move(_next_l);
                            _loop_fuel = std::move(_next_fuel);
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
                            std::shared_ptr<List<unsigned int>> _next_l =
                                _args.d_a1;
                            unsigned int _next_fuel = fuel_;
                            _loop_l = std::move(_next_l);
                            _loop_fuel = std::move(_next_fuel);
                          }
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
  }
  return _head;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::uniq_sorted(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return uniq_sorted_fuel(len, l);
}

__attribute__((pure)) unsigned int
LoopifyListTransforms::step_sum(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
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
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil &)
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons &_args)
                                 -> void {
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
