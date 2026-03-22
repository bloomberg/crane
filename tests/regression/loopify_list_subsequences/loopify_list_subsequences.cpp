#include <loopify_list_subsequences.h>

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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::map_cons_helper(
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
                          -> void {
                        _result = List<
                            std::shared_ptr<List<unsigned int>>>::ctor::Nil_();
                      },
                      [&](const typename List<
                          std::shared_ptr<List<unsigned int>>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{
                            List<unsigned int>::ctor::Cons_(x, _args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1});
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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::tails(std::shared_ptr<List<unsigned int>> l) {
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
                          -> void {
                        _result = List<std::shared_ptr<List<unsigned int>>>::
                            ctor::Cons_(
                                List<unsigned int>::ctor::Nil_(),
                                List<std::shared_ptr<List<unsigned int>>>::
                                    ctor::Nil_());
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{std::move(l)});
                        _stack.push_back(_Enter{_args.d_a1});
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

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::inits_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
                    List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                        List<unsigned int>::ctor::Nil_(),
                        List<
                            std::shared_ptr<List<unsigned int>>>::ctor::Nil_());
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          _result = List<std::shared_ptr<List<unsigned int>>>::
                              ctor::Cons_(
                                  List<unsigned int>::ctor::Nil_(),
                                  List<std::shared_ptr<List<unsigned int>>>::
                                      ctor::Nil_());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args});
                          _stack.push_back(_Enter{_args.d_a1, fuel_});
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> rest =
                  _result;
              _result = List<std::shared_ptr<List<unsigned int>>>::ctor::Cons_(
                  List<unsigned int>::ctor::Nil_(),
                  map_cons_helper(_args.d_a0, std::move(rest)));
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>
LoopifyListSubsequences::inits(const std::shared_ptr<List<unsigned int>> &l) {
  return inits_fuel(l->length(), l);
}

std::shared_ptr<List<unsigned int>> LoopifyListSubsequences::init_list(
    const std::shared_ptr<List<unsigned int>> &l) {
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
                          -> void {
                        _result = List<unsigned int>::ctor::Nil_();
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> void {
                                  _result = List<unsigned int>::ctor::Nil_();
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> void {
                                  _stack.push_back(_Call1{_args.d_a0});
                                  _stack.push_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
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

std::shared_ptr<List<unsigned int>>
LoopifyListSubsequences::snoc(const std::shared_ptr<List<unsigned int>> &l,
                              const unsigned int x) {
  struct _Enter {
    const unsigned int x;
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{x, l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int x = _f.x;
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> void {
                        _result = List<unsigned int>::ctor::Cons_(
                            std::move(x), List<unsigned int>::ctor::Nil_());
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{std::move(x), _args.d_a1});
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

__attribute__((pure)) unsigned int LoopifyListSubsequences::last_elem(
    const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args) {
              _result = 0u;
              _continue = false;
            },
            [&](const typename List<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args0) {
                        _result = _args.d_a0;
                        _continue = false;
                      },
                      [&](const typename List<unsigned int>::Cons _args0) {
                        _loop_l = _args.d_a1;
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyListSubsequences::nth_elem(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename List<unsigned int>::Nil _args) {
                     _result = 0u;
                     _continue = false;
                   },
                   [&](const typename List<unsigned int>::Cons _args) {
                     if (_loop_n == 0u) {
                       _result = _args.d_a0;
                       _continue = false;
                     } else {
                       std::shared_ptr<List<unsigned int>> _next_l = _args.d_a1;
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

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListSubsequences::split_at(const unsigned int n,
                                  std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int n;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<List<unsigned int>>,
            std::shared_ptr<List<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int n = _f.n;
              if (n <= 0) {
                _result = std::make_pair(List<unsigned int>::ctor::Nil_(),
                                         std::move(l));
              } else {
                unsigned int n_ = n - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          _result =
                              std::make_pair(List<unsigned int>::ctor::Nil_(),
                                             List<unsigned int>::ctor::Nil_());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          _stack.push_back(_Call1{_args});
                          _stack.push_back(_Enter{_args.d_a1, n_});
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              const typename List<unsigned int>::Cons _args = _f._s0;
              std::shared_ptr<List<unsigned int>> before = _result.first;
              std::shared_ptr<List<unsigned int>> after = _result.second;
              _result = std::make_pair(
                  List<unsigned int>::ctor::Cons_(_args.d_a0, before), after);
            }},
        _frame);
  }
  return _result;
}
