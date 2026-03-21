#include <loopify_sorting.h>

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

/// Consolidated UNIQUE sorting algorithms and related operations.
std::shared_ptr<List<unsigned int>>
LoopifySorting::insert(const unsigned int x,
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
        Overloaded{[&](_Enter _f) {
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
                               _stack.push_back(_Call1{_args.d_a0});
                               _stack.push_back(_Enter{_args.d_a1});
                               return {};
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
                unsigned int f = fuel - 1;
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
                                      _stack.push_back(_Enter{std::move(l2),
                                                              _args.d_a1,
                                                              std::move(f)});
                                    } else {
                                      _stack.push_back(_Call2{_args0.d_a0});
                                      _stack.push_back(_Enter{_args0.d_a1, l1,
                                                              std::move(f)});
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
                                    _result = l;
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<unsigned int>> {
                                    std::shared_ptr<List<unsigned int>> l1 =
                                        split<unsigned int>(l).first;
                                    std::shared_ptr<List<unsigned int>> l2 =
                                        split<unsigned int>(l).second;
                                    _stack.push_back(_Call1{l1, f});
                                    _stack.push_back(_Enter{l2, f});
                                    return {};
                                  }},
                              _args.d_a1->v());
                          return {};
                        }},
                    l->v());
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<unsigned int>> l = _f.l;
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
                        _stack.push_back(_Call1{pivot, _args});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
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
                    List<unsigned int>::ctor::Cons_(_args.d_a0, lo), hi);
              } else {
                _result = std::make_pair(
                    lo, List<unsigned int>::ctor::Cons_(_args.d_a0, hi));
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
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          _result = List<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename List<unsigned int>::Cons _args)
                            -> std::shared_ptr<List<unsigned int>> {
                          std::shared_ptr<List<unsigned int>> lo =
                              partition(_args.d_a0, _args.d_a1).first;
                          std::shared_ptr<List<unsigned int>> hi =
                              partition(_args.d_a0, _args.d_a1).second;
                          _stack.push_back(_Call1{lo, f, _args.d_a0});
                          _stack.push_back(_Enter{hi, f});
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s2});
              _stack.push_back(_Enter{_f._s0, _f._s1});
            },
            [&](_Call2 _f) {
              _result =
                  _result->app(List<unsigned int>::ctor::Cons_(_f._s1, _f._s0));
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
                                    _stack.push_back(_Enter{_args.d_a1});
                                  } else {
                                    _stack.push_back(_Call1{_args.d_a0});
                                    _stack.push_back(_Enter{_args.d_a1});
                                  }
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

/// uniq_sorted variant that preserves order.
std::shared_ptr<List<unsigned int>>
LoopifySorting::uniq_sorted_aux(const unsigned int prev, const bool seen,
                                const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
    const bool seen;
    const unsigned int prev;
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
  _stack.push_back(_Enter{l, seen, prev});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const bool seen = _f.seen;
                     const unsigned int prev = _f.prev;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = List<unsigned int>::ctor::Nil_();
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               if (seen) {
                                 if (prev == _args.d_a0) {
                                   _stack.push_back(
                                       _Enter{_args.d_a1, true, _args.d_a0});
                                 } else {
                                   _stack.push_back(_Call1{_args.d_a0});
                                   _stack.push_back(
                                       _Enter{_args.d_a1, true, _args.d_a0});
                                 }
                               } else {
                                 _stack.push_back(_Call2{_args.d_a0});
                                 _stack.push_back(
                                     _Enter{_args.d_a1, true, _args.d_a0});
                               }
                               return {};
                             }},
                         l->v());
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
LoopifySorting::uniq_sorted(const std::shared_ptr<List<unsigned int>> &l) {
  return uniq_sorted_aux(0u, false, l);
}
