#include <loopify_list_windows.h>

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

__attribute__((pure)) unsigned int
LoopifyListWindows::len(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
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
                               _stack.push_back(_Call1{1u});
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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::map_cons_helper(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(List<unsigned int>::ctor::Cons_(
        std::declval<const unsigned int &>(),
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{ll});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  ll = _f.ll;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _result = List<
                            std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _stack.push_back(_Call1{
                            List<unsigned int>::ctor::Cons_(x, _args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListWindows::drop(const unsigned int m,
                         std::shared_ptr<List<unsigned int>> xs) {
  std::shared_ptr<List<unsigned int>> _result;
  std::shared_ptr<List<unsigned int>> _loop_xs = xs;
  unsigned int _loop_m = m;
  bool _continue = true;
  while (_continue) {
    if (_loop_m <= 0) {
      {
        _result = std::move(_loop_xs);
        _continue = false;
      }
    } else {
      unsigned int m_ = _loop_m - 1;
      std::visit(Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                              _result = List<unsigned int>::ctor::Nil_();
                              _continue = false;
                            },
                            [&](const typename List<unsigned int>::Cons _args) {
                              std::shared_ptr<List<unsigned int>> _next_xs =
                                  _args.d_a1;
                              unsigned int _next_m = std::move(m_);
                              _loop_xs = std::move(_next_xs);
                              _loop_m = std::move(_next_m);
                            }},
                 _loop_xs->v());
    }
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListWindows::span_eq(const unsigned int first,
                            std::shared_ptr<List<unsigned int>> lst) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> lst;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{lst});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> lst = _f.lst;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::pair<std::shared_ptr<List<unsigned int>>,
                                       std::shared_ptr<List<unsigned int>>> {
                        _result =
                            std::make_pair(List<unsigned int>::ctor::Nil_(),
                                           List<unsigned int>::ctor::Nil_());
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::pair<std::shared_ptr<List<unsigned int>>,
                                       std::shared_ptr<List<unsigned int>>> {
                        if (first == _args.d_a0) {
                          _stack.push_back(_Call1{_args});
                          _stack.push_back(_Enter{_args.d_a1});
                        } else {
                          _result = std::make_pair(
                              List<unsigned int>::ctor::Nil_(), std::move(lst));
                        }
                        return {};
                      }},
                  lst->v());
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> s = _result.first;
              std::shared_ptr<List<unsigned int>> r = _result.second;
              _result = std::make_pair(
                  List<unsigned int>::ctor::Cons_(_args.d_a0, s), r);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListWindows::differences(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype((
        ((std::declval<const typename List<unsigned int>::Cons &>().d_a0 -
          std::declval<const typename List<unsigned int>::Cons &>().d_a0) >
                 std::declval<const typename List<unsigned int>::Cons &>().d_a0
             ? 0
             : (std::declval<const typename List<unsigned int>::Cons &>().d_a0 -
                std::declval<const typename List<unsigned int>::Cons &>()
                    .d_a0)))) _s0;
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
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              unsigned int>::Nil _args1)
                                              -> std::shared_ptr<
                                                  List<unsigned int>> {
                                            _result = List<
                                                unsigned int>::ctor::Nil_();
                                            return {};
                                          },
                                          [&](const typename List<
                                              unsigned int>::Cons _args1)
                                              -> std::shared_ptr<
                                                  List<unsigned int>> {
                                            _stack.push_back(_Call1{
                                                (((_args1.d_a0 - _args.d_a0) >
                                                          _args1.d_a0
                                                      ? 0
                                                      : (_args1.d_a0 -
                                                         _args.d_a0)))});
                                            _stack.push_back(
                                                _Enter{_args.d_a1});
                                            return {};
                                          }},
                                      _args.d_a1->v());
                                  return {};
                                }},
                            _args.d_a1->v());
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
LoopifyListWindows::sliding_pairs(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
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
                                      std::pair<unsigned int,
                                                unsigned int>>::ctor::Nil_();
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0)
                                    -> std::shared_ptr<List<std::pair<
                                        unsigned int, unsigned int>>> {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename List<
                                              unsigned int>::Nil _args1)
                                              -> std::shared_ptr<List<
                                                  std::pair<unsigned int,
                                                            unsigned int>>> {
                                            _result =
                                                List<std::pair<unsigned int,
                                                               unsigned int>>::
                                                    ctor::Nil_();
                                            return {};
                                          },
                                          [&](const typename List<
                                              unsigned int>::Cons _args1)
                                              -> std::shared_ptr<List<
                                                  std::pair<unsigned int,
                                                            unsigned int>>> {
                                            _stack.push_back(
                                                _Call1{std::make_pair(
                                                    _args.d_a0, _args1.d_a0)});
                                            _stack.push_back(
                                                _Enter{_args.d_a1});
                                            return {};
                                          }},
                                      _args.d_a1->v());
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  l->v());
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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::inits(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(List<unsigned int>::ctor::Nil_()) _s0;
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
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
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _result = List<std::shared_ptr<List<unsigned int>>>::
                            ctor::Cons_(
                                List<unsigned int>::ctor::Nil_(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    ctor::Nil_());
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _stack.push_back(_Call1{
                            List<unsigned int>::ctor::Nil_(), _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  _f._s0, map_cons_helper(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::tails(std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _result = List<std::shared_ptr<List<unsigned int>>>::
                            ctor::Cons_(
                                List<unsigned int>::ctor::Nil_(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    ctor::Nil_());
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<
                              List<std::shared_ptr<List<unsigned int>>>> {
                        _stack.push_back(_Call1{std::move(l)});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyListWindows::take(const unsigned int n,
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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::windows_fuel(const unsigned int fuel, const unsigned int n,
                                 std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(take(
        std::declval<const unsigned int &>(),
        std::move(std::declval<std::shared_ptr<List<unsigned int>> &>()))) _s0;
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
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          _result = List<std::shared_ptr<List<unsigned int>>>::
                              ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          if (len(l) < n) {
                            _result =
                                List<std::shared_ptr<List<unsigned int>>>::
                                    ctor::Nil_();
                          } else {
                            _stack.push_back(_Call1{take(n, std::move(l))});
                            _stack.push_back(
                                _Enter{_args.d_a1, std::move(fuel_)});
                          }
                          return {};
                        }},
                    l->v());
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
LoopifyListWindows::windows(const unsigned int n,
                            const std::shared_ptr<List<unsigned int>> &l) {
  return windows_fuel(len(l), n, l);
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::chunks_fuel(const unsigned int fuel, const unsigned int n,
                                const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
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
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          _result = List<std::shared_ptr<List<unsigned int>>>::
                              ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          std::shared_ptr<List<unsigned int>> chunk =
                              take(n, l);
                          std::shared_ptr<List<unsigned int>> rest =
                              drop(n, std::move(l));
                          _stack.push_back(_Call1{std::move(chunk)});
                          _stack.push_back(_Enter{std::move(rest), fuel_});
                          return {};
                        }},
                    l->v());
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
LoopifyListWindows::chunks(const unsigned int n,
                           const std::shared_ptr<List<unsigned int>> &l) {
  return chunks_fuel(len(l), n, l);
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListWindows::group_fuel(const unsigned int fuel,
                               const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(List<unsigned int>::ctor::Cons_(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
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
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          _result = List<std::shared_ptr<List<unsigned int>>>::
                              ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<
                                List<std::shared_ptr<List<unsigned int>>>> {
                          std::shared_ptr<List<unsigned int>> same =
                              span_eq(_args.d_a0, _args.d_a1).first;
                          std::shared_ptr<List<unsigned int>> rest =
                              span_eq(_args.d_a0, _args.d_a1).second;
                          _stack.push_back(
                              _Call1{List<unsigned int>::ctor::Cons_(_args.d_a0,
                                                                     same)});
                          _stack.push_back(_Enter{rest, fuel_});
                          return {};
                        }},
                    l->v());
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
LoopifyListWindows::group(const std::shared_ptr<List<unsigned int>> &l) {
  return group_fuel(len(l), l);
}
