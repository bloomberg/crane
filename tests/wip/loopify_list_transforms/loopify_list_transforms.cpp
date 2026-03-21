#include <loopify_list_transforms.h>

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
                          -> std::shared_ptr<
                              List<std::pair<unsigned int, unsigned int>>> {
                        _result = List<std::pair<unsigned int,
                                                 unsigned int>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<
                              List<std::pair<unsigned int, unsigned int>>> {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0)
                                    -> std::shared_ptr<List<std::pair<
                                        unsigned int, unsigned int>>> {
                                  _result = List<
                                      std::pair<unsigned int, unsigned int>>::
                                      ctor::Cons_(
                                          std::make_pair(_args.d_a0, 1u),
                                          List<std::pair<unsigned int,
                                                         unsigned int>>::ctor::
                                              Nil_());
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0)
                                    -> std::shared_ptr<List<std::pair<
                                        unsigned int, unsigned int>>> {
                                  _stack.push_back(_Call1{_args});
                                  _stack.push_back(_Enter{_args.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Nil _args1)
                          -> void {
                        _result = List<std::pair<unsigned int, unsigned int>>::
                            ctor::Cons_(
                                std::make_pair(_args.d_a0, 1u),
                                List<std::pair<unsigned int,
                                               unsigned int>>::ctor::Nil_());
                      },
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Cons _args1)
                          -> void {
                        unsigned int y = _args1.d_a0.first;
                        unsigned int n = _args1.d_a0.second;
                        if (_args.d_a0 == y) {
                          _result =
                              List<std::pair<unsigned int, unsigned int>>::
                                  ctor::Cons_(std::make_pair(y, (n + 1u)),
                                              _args1.d_a1);
                        } else {
                          _result = List<
                              std::pair<unsigned int, unsigned int>>::ctor::
                              Cons_(
                                  std::make_pair(_args.d_a0, 1u),
                                  List<std::pair<unsigned int, unsigned int>>::
                                      ctor::Cons_(std::make_pair(y, n),
                                                  _args1.d_a1));
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
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int acc;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, acc});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int acc = _f.acc;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = List<unsigned int>::ctor::Cons_(
                                   std::move(acc),
                                   List<unsigned int>::ctor::Nil_());
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _stack.push_back(_Call1{acc});
                               _stack.push_back(
                                   _Enter{_args.d_a1, (acc + _args.d_a0)});
                               return {};
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) {
                     _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::sliding_pairs_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    List<std::pair<unsigned int, unsigned int>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<
                                List<std::pair<unsigned int, unsigned int>>> {
                          _result = List<std::pair<unsigned int,
                                                   unsigned int>>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<
                                List<std::pair<unsigned int, unsigned int>>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0)
                                      -> std::shared_ptr<List<std::pair<
                                          unsigned int, unsigned int>>> {
                                    _result = List<
                                        std::pair<unsigned int,
                                                  unsigned int>>::ctor::Nil_();
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<std::pair<
                                          unsigned int, unsigned int>>> {
                                    _stack.push_back(_Call1{std::make_pair(
                                        _args.d_a0, _args0.d_a0)});
                                    _stack.push_back(_Enter{_args.d_a1, fuel_});
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result =
                  List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListTransforms::sliding_pairs(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return sliding_pairs_fuel(std::move(len), l);
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
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(abs_diff(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = List<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    _result = List<unsigned int>::ctor::Nil_();
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    _stack.push_back(_Call1{
                                        abs_diff(_args.d_a0, _args0.d_a0)});
                                    _stack.push_back(_Enter{_args.d_a1, fuel_});
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::differences(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return differences_fuel(std::move(len), l);
}

std::shared_ptr<List<unsigned int>>
LoopifyListTransforms::take(const unsigned int n,
                            const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int n;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int n = _f.n;
              if (n <= 0) {
                _result = List<unsigned int>::ctor::Nil_();
              } else {
                unsigned int n_ = n - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = List<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1, n_});
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
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
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = List<unsigned int>::ctor::Nil_();
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              std::shared_ptr<List<unsigned int>> _next_l =
                                  _args.d_a1;
                              unsigned int _next_n = std::move(n_);
                              _loop_l = std::move(_next_l);
                              _loop_n = std::move(_next_n);
                            }},
                 _loop_l->v());
    }
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListTransforms::chunks_of_fuel(const unsigned int fuel,
                                      const unsigned int n,
                                      std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(take(std::declval<const unsigned int &>(),
                  std::declval<std::shared_ptr<List<unsigned int>> &>())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
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
                _result =
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                if (n <= 0u) {
                  _result =
                      List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
                } else {
                  std::visit(
                      Overloaded{
                          [&](const typename List<unsigned int>::Nil _args)
                              -> std::shared_ptr<
                                  List<std::shared_ptr<List<unsigned int>>>> {
                            _result =
                                List<std::shared_ptr<List<unsigned int>>>::
                                    ctor::Nil_();
                            return {};
                          },
                          [&](const typename List<unsigned int>::Cons _args)
                              -> std::shared_ptr<
                                  List<std::shared_ptr<List<unsigned int>>>> {
                            _stack.push_back(_Call1{take(n, l)});
                            _stack.push_back(
                                _Enter{drop(n, l), std::move(fuel_)});
                            return {};
                          }},
                      l->v());
                }
              }
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListTransforms::chunks_of(const unsigned int n,
                                 const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return chunks_of_fuel(std::move(len), n, l);
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
          _result = _loop_l;
          _continue = false;
        }
      } else {
        std::visit(
            Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                         _result = List<unsigned int>::ctor::Nil_();
                         _continue = false;
                       },
                       [&](const typename List<unsigned int>::Cons _args) {
                         std::shared_ptr<List<unsigned int>> rotated =
                             _args.d_a1->app(List<unsigned int>::ctor::Cons_(
                                 _args.d_a0, List<unsigned int>::ctor::Nil_()));
                         std::shared_ptr<List<unsigned int>> _next_l =
                             std::move(rotated);
                         unsigned int _next_n =
                             (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                         unsigned int _next_fuel = std::move(fuel_);
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

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::rotate_left(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  return rotate_left_fuel((n + 1u), n, l);
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::uniq_sorted_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = List<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    _result = List<unsigned int>::ctor::Cons_(
                                        _args.d_a0,
                                        List<unsigned int>::ctor::Nil_());
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    if (_args.d_a0 == _args0.d_a0) {
                                      _stack.push_back(
                                          _Enter{_args.d_a1, fuel_});
                                    } else {
                                      _stack.push_back(_Call1{_args.d_a0});
                                      _stack.push_back(
                                          _Enter{_args.d_a1, fuel_});
                                    }
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListTransforms::uniq_sorted(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return uniq_sorted_fuel(std::move(len), l);
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
                                 -> unsigned int {
                               _result = 0u;
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> unsigned int {
                               unsigned int contribution;
                               if ((_args.d_a0 % 2u) == 0u) {
                                 contribution = _args.d_a0;
                               } else {
                                 contribution = (_args.d_a0 * 2u);
                               }
                               _stack.push_back(
                                   _Call1{std::move(contribution)});
                               _stack.push_back(_Enter{_args.d_a1});
                               return {};
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}
