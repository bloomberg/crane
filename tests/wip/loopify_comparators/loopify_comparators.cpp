#include <loopify_comparators.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
LoopifyComparators::maximum_by(const std::shared_ptr<List<unsigned int>> &l) {
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
        Overloaded{
            [&](_Enter _f) {
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
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> unsigned int {
                                  _result = _args.d_a0;
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> unsigned int {
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
              unsigned int m = _result;
              if (m < _args.d_a0) {
                _result = _args.d_a0;
              } else {
                _result = std::move(m);
              }
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyComparators::minimum_by(const std::shared_ptr<List<unsigned int>> &l) {
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
        Overloaded{
            [&](_Enter _f) {
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
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil
                                        _args0) -> unsigned int {
                                  _result = _args.d_a0;
                                  return {};
                                },
                                [&](const typename List<unsigned int>::Cons
                                        _args0) -> unsigned int {
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
              unsigned int m = _result;
              if (_args.d_a0 < m) {
                _result = _args.d_a0;
              } else {
                _result = std::move(m);
              }
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyComparators::merge_by_fuel(const unsigned int fuel,
                                  std::shared_ptr<List<unsigned int>> l1,
                                  std::shared_ptr<List<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l2;
    std::shared_ptr<List<unsigned int>> l1;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = List<unsigned int>::ctor::Nil_();
              } else {
                unsigned int fuel_ = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = std::move(l2);
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename List<unsigned int>::Nil
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    _result = l1;
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    if (_args.d_a0 <= _args0.d_a0) {
                                      _stack.push_back(_Call1{_args.d_a0});
                                      _stack.push_back(
                                          _Enter{std::move(l2), _args.d_a1,
                                                 std::move(fuel_)});
                                    } else {
                                      _stack.push_back(_Call2{_args0.d_a0});
                                      _stack.push_back(_Enter{
                                          _args0.d_a1, l1, std::move(fuel_)});
                                    }
                                    return {};
                                  }},
                              l2->v());
                          return {};
                        }},
                    l1->v());
              }
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            },
            [&](_Call2 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyComparators::merge_by(const std::shared_ptr<List<unsigned int>> &l1,
                             const std::shared_ptr<List<unsigned int>> &l2) {
  unsigned int len1 = l1->length();
  unsigned int len2 = l2->length();
  return merge_by_fuel((std::move(len1) + std::move(len2)), l1, l2);
}

std::shared_ptr<List<unsigned int>>
LoopifyComparators::insert_sorted(const unsigned int x,
                                  std::shared_ptr<List<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<List<unsigned int>> l;
    const unsigned int x;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, x});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<List<unsigned int>> l = _f.l;
              const unsigned int x = _f.x;
              std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Cons_(
                            std::move(x), List<unsigned int>::ctor::Nil_());
                        return {};
                      },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        if (x <= _args.d_a0) {
                          _result = List<unsigned int>::ctor::Cons_(
                              std::move(x), std::move(l));
                        } else {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1, std::move(x)});
                        }
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

std::shared_ptr<List<unsigned int>> LoopifyComparators::insertion_sort(
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
                  Overloaded{[&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = List<unsigned int>::ctor::Nil_();
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _stack.push_back(_Call1{_args.d_a0});
                               _stack.push_back(_Enter{_args.d_a1});
                               return {};
                             }},
                  l->v());
            },
            [&](_Call1 _f) { _result = insert_sorted(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyComparators::is_sorted_fuel(
    const unsigned int fuel, const std::shared_ptr<List<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<List<unsigned int>> _loop_l = l;
  unsigned int _loop_fuel = fuel;
  bool _continue = true;
  while (_continue) {
    if (_loop_fuel <= 0) {
      {
        _result = true;
        _continue = false;
      }
    } else {
      unsigned int fuel_ = _loop_fuel - 1;
      std::visit(
          Overloaded{
              [&](const typename List<unsigned int>::Nil _args) {
                _result = true;
                _continue = false;
              },
              [&](const typename List<unsigned int>::Cons _args) {
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args0) {
                          _result = true;
                          _continue = false;
                        },
                        [&](const typename List<unsigned int>::Cons _args0) {
                          if (_args.d_a0 <= _args0.d_a0) {
                            std::shared_ptr<List<unsigned int>> _next_l =
                                List<unsigned int>::ctor::Cons_(_args0.d_a0,
                                                                _args0.d_a1);
                            unsigned int _next_fuel = fuel_;
                            _loop_l = std::move(_next_l);
                            _loop_fuel = std::move(_next_fuel);
                          } else {
                            _result = false;
                            _continue = false;
                          }
                        }},
                    _args.d_a1->v());
              }},
          _loop_l->v());
    }
  }
  return _result;
}

__attribute__((pure)) bool
LoopifyComparators::is_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  unsigned int len = l->length();
  return is_sorted_fuel(std::move(len), l);
}
