#include <loopify_list_of_lists.h>

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

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::intercalate(
    const std::shared_ptr<List<unsigned int>> &sep,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<List<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
    const std::shared_ptr<List<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Nil
                                        _args0) -> void {
                                  _result = _args.d_a0;
                                },
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_f._s1->app(_result)); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::map_hd(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _stack.push_back(_Enter{_args.d_a1});
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args0.d_a0});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a0->v());
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListOfLists::map_tl(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a1) _s0;
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
                          -> void {
                        _result = List<
                            std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _stack.push_back(_Enter{_args.d_a1});
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args0.d_a1});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a0->v());
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

__attribute__((pure)) bool LoopifyListOfLists::all_empty(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  bool _result;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    _args) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _loop_ll = _args.d_a1;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        _result = false;
                        _continue = false;
                      }},
                  _args.d_a0->v());
            }},
        _loop_ll->v());
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListOfLists::transpose_fuel(
    const unsigned int fuel,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{ll, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  ll = _f.ll;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<
                            std::shared_ptr<List<unsigned int>>>::Nil _args)
                            -> void {
                          _result = List<std::shared_ptr<List<unsigned int>>>::
                              ctor::Nil_();
                        },
                        [&](const typename List<
                            std::shared_ptr<List<unsigned int>>>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> void {
                                    _result = List<std::shared_ptr<
                                        List<unsigned int>>>::ctor::Nil_();
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> void {
                                    if (all_empty(ll)) {
                                      _result = List<std::shared_ptr<
                                          List<unsigned int>>>::ctor::Nil_();
                                    } else {
                                      std::shared_ptr<List<unsigned int>>
                                          heads = map_hd(ll);
                                      std::shared_ptr<List<
                                          std::shared_ptr<List<unsigned int>>>>
                                          tails = map_tl(ll);
                                      _stack.push_back(
                                          _Call1{std::move(heads)});
                                      _stack.push_back(
                                          _Enter{std::move(tails), fuel_});
                                    }
                                  }},
                              _args.d_a0->v());
                        }},
                    ll->v());
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

__attribute__((pure)) unsigned int
LoopifyListOfLists::list_len(const std::shared_ptr<List<unsigned int>> &l) {
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
                                 -> void { _result = 0u; },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> void {
                               _stack.push_back(_Call1{1u});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListOfLists::total_length(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(list_len(
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                          -> void { _result = 0u; },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{list_len(_args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListOfLists::transpose(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  return transpose_fuel(total_length(ll), ll);
}

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::flatten(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<
                 std::shared_ptr<List<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListOfLists::count_total(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(list_len(
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                          -> void { _result = 0u; },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{list_len(_args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyListOfLists::firsts(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
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
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _stack.push_back(_Enter{_args.d_a1});
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args0.d_a0});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a0->v());
                      }},
                  ll->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyListOfLists::all_nil(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  bool _result;
  std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> _loop_ll = ll;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Nil
                    _args) {
              _result = true;
              _continue = false;
            },
            [&](const typename List<std::shared_ptr<List<unsigned int>>>::Cons
                    _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _loop_ll = _args.d_a1;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        _result = false;
                        _continue = false;
                      }},
                  _args.d_a0->v());
            }},
        _loop_ll->v());
  }
  return _result;
}

std::shared_ptr<List<std::pair<std::shared_ptr<List<unsigned int>>,
                               std::shared_ptr<List<unsigned int>>>>>
LoopifyListOfLists::zip_lists(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll1,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll2) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll2;
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll1;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0,
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<std::pair<std::shared_ptr<List<unsigned int>>,
                                 std::shared_ptr<List<unsigned int>>>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{ll2, ll1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  ll2 = _f.ll2;
              const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
                  ll1 = _f.ll1;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Nil _args)
                          -> void {
                        _result = List<std::pair<
                            std::shared_ptr<List<unsigned int>>,
                            std::shared_ptr<List<unsigned int>>>>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Nil
                                        _args0) -> void {
                                  _result = List<std::pair<
                                      std::shared_ptr<List<unsigned int>>,
                                      std::shared_ptr<List<unsigned int>>>>::
                                      ctor::Nil_();
                                },
                                [&](const typename List<
                                    std::shared_ptr<List<unsigned int>>>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{
                                      std::make_pair(_args.d_a0, _args0.d_a0)});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                }},
                            ll2->v());
                      }},
                  ll1->v());
            },
            [&](_Call1 _f) {
              _result = List<std::pair<std::shared_ptr<List<unsigned int>>,
                                       std::shared_ptr<List<unsigned int>>>>::
                  ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListOfLists::max_length(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ll) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ll;
  };

  struct _Call1 {
    decltype(list_len(
        std::declval<
            const typename List<std::shared_ptr<List<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                          -> void { _result = 0u; },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{list_len(_args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  ll->v());
            },
            [&](_Call1 _f) { _result = std::max(_f._s0, _result); }},
        _frame);
  }
  return _result;
}
