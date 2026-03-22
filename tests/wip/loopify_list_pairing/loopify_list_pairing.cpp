#include <loopify_list_pairing.h>

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

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::unzip(
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Nil _args)
                          -> void {
                        _result =
                            std::make_pair(List<unsigned int>::ctor::Nil_(),
                                           List<unsigned int>::ctor::Nil_());
                      },
                      [&](const typename List<
                          std::pair<unsigned int, unsigned int>>::Cons _args)
                          -> void {
                        unsigned int a = _args.d_a0.first;
                        unsigned int b = _args.d_a0.second;
                        _stack.push_back(_Call1{b, a});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              unsigned int b = _f._s0;
              unsigned int a = _f._s1;
              std::shared_ptr<List<unsigned int>> xs = _result.first;
              std::shared_ptr<List<unsigned int>> ys = _result.second;
              _result = std::make_pair(List<unsigned int>::ctor::Cons_(a, xs),
                                       List<unsigned int>::ctor::Cons_(b, ys));
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::swizzle(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = std::make_pair(
                                   List<unsigned int>::ctor::Nil_(),
                                   List<unsigned int>::ctor::Nil_());
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
              std::shared_ptr<List<unsigned int>> odds = _result.first;
              std::shared_ptr<List<unsigned int>> evens = _result.second;
              _result = std::make_pair(
                  List<unsigned int>::ctor::Cons_(_args.d_a0, evens), odds);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::partition(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = std::make_pair(
                                   List<unsigned int>::ctor::Nil_(),
                                   List<unsigned int>::ctor::Nil_());
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
              std::shared_ptr<List<unsigned int>> yes = _result.first;
              std::shared_ptr<List<unsigned int>> no = _result.second;
              if ((_args.d_a0 % 2u) == 0u) {
                _result = std::make_pair(
                    List<unsigned int>::ctor::Cons_(_args.d_a0, yes), no);
              } else {
                _result = std::make_pair(
                    yes, List<unsigned int>::ctor::Cons_(_args.d_a0, no));
              }
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListPairing::zip_longest_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2,
    const unsigned int default0) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<const unsigned int &>(),
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  struct _Call2 {
    decltype(std::make_pair(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const unsigned int &>())) _s0;
  };

  struct _Call3 {
    decltype(std::make_pair(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  std::shared_ptr<List<std::pair<unsigned int, unsigned int>>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    List<std::pair<unsigned int, unsigned int>>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> void {
                                    _result = List<
                                        std::pair<unsigned int,
                                                  unsigned int>>::ctor::Nil_();
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> void {
                                    _stack.push_back(_Call1{
                                        std::make_pair(default0, _args0.d_a0)});
                                    _stack.push_back(
                                        _Enter{_args0.d_a1,
                                               List<unsigned int>::ctor::Nil_(),
                                               std::move(fuel_)});
                                  }},
                              l2->v());
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> void {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0) -> void {
                                    _stack.push_back(_Call2{
                                        std::make_pair(_args.d_a0, default0)});
                                    _stack.push_back(
                                        _Enter{List<unsigned int>::ctor::Nil_(),
                                               _args.d_a1, std::move(fuel_)});
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0) -> void {
                                    _stack.push_back(_Call3{std::make_pair(
                                        _args.d_a0, _args0.d_a0)});
                                    _stack.push_back(_Enter{_args0.d_a1,
                                                            _args.d_a1,
                                                            std::move(fuel_)});
                                  }},
                              l2->v());
                        }},
                    l1->v());
              }
            },
            [&](_Call1 _f) {
              _result =
                  List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      _f._s0, _result);
            },
            [&](_Call2 _f) {
              _result =
                  List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      _f._s0, _result);
            },
            [&](_Call3 _f) {
              _result =
                  List<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyListPairing::zip_longest(const std::shared_ptr<List<unsigned int>> &l1,
                                const std::shared_ptr<List<unsigned int>> &l2,
                                const unsigned int default0) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  unsigned int maxlen;
  if (len1 < len2) {
    maxlen = len2;
  } else {
    maxlen = len1;
  }
  return zip_longest_fuel(std::move(maxlen), l1, l2, default0);
}

std::shared_ptr<List<unsigned int>>
LoopifyListPairing::zipWith(const std::shared_ptr<List<unsigned int>> &l1,
                            const std::shared_ptr<List<unsigned int>> &l2) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
  };

  struct _Call1 {
    decltype((
        std::declval<const typename List<unsigned int>::Cons &>().d_a0 +
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
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
                                  _stack.push_back(
                                      _Call1{(_args.d_a0 + _args0.d_a0)});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                }},
                            l2->v());
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<std::shared_ptr<List<unsigned int>>,
                                std::shared_ptr<List<unsigned int>>>
LoopifyListPairing::split_even_odd(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> void {
                               _result = std::make_pair(
                                   List<unsigned int>::ctor::Nil_(),
                                   List<unsigned int>::ctor::Nil_());
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
              std::shared_ptr<List<unsigned int>> evens = _result.first;
              std::shared_ptr<List<unsigned int>> odds = _result.second;
              if ((_args.d_a0 % 2u) == 0u) {
                _result = std::make_pair(
                    List<unsigned int>::ctor::Cons_(_args.d_a0, evens), odds);
              } else {
                _result = std::make_pair(
                    evens, List<unsigned int>::ctor::Cons_(_args.d_a0, odds));
              }
            }},
        _frame);
  }
  return _result;
}
