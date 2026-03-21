#include <loopify_lists.h>

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

/// Consolidated UNIQUE list operations - no stdlib duplicates.
/// Tests loopification on domain-specific list algorithms.
/// range start count generates start, start+1, ..., start+count-1.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::range(const unsigned int start, const unsigned int count0) {
  struct _Enter {
    const unsigned int count0;
    const unsigned int start;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{count0, start});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int count0 = _f.count0;
                            const unsigned int start = _f.start;
                            if (count0 <= 0) {
                              _result = list<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int c = count0 - 1;
                              _stack.push_back(_Call1{start});
                              _stack.push_back(_Enter{c, (start + 1)});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = list<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}

/// step_sum l sums with conditional contributions: even values as-is, odd
/// doubled.
__attribute__((pure)) unsigned int LoopifyLists::step_sum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        unsigned int contribution;
                        if ((_args.d_a0 % 2u) == 0u) {
                          contribution = _args.d_a0;
                        } else {
                          contribution = (_args.d_a0 * 2u);
                        }
                        _stack.push_back(_Call1{std::move(contribution)});
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

/// sum_abs l sums absolute values (using monus for nat).
__attribute__((pure)) unsigned int LoopifyLists::sum_abs(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
    const unsigned int base) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        unsigned int abs_val;
                        if (base <= _args.d_a0) {
                          abs_val = (((_args.d_a0 - base) > _args.d_a0
                                          ? 0
                                          : (_args.d_a0 - base)));
                        } else {
                          abs_val = (((base - _args.d_a0) > base
                                          ? 0
                                          : (base - _args.d_a0)));
                        }
                        _stack.push_back(_Call1{std::move(abs_val)});
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

/// four_elem l multi-case pattern matching on list structure.
__attribute__((pure)) unsigned int LoopifyLists::four_elem(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype((
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0 +
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
    decltype((
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0 +
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s1;
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
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0) -> unsigned int {
                                  _result = 1u;
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> unsigned int {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename LoopifyLists::list<
                                              unsigned int>::Nil _args1)
                                              -> unsigned int {
                                            _result = 2u;
                                            return {};
                                          },
                                          [&](const typename LoopifyLists::list<
                                              unsigned int>::Cons _args1)
                                              -> unsigned int {
                                            std::visit(
                                                Overloaded{
                                                    [&](const typename LoopifyLists::
                                                            list<unsigned int>::
                                                                Nil _args2)
                                                        -> unsigned int {
                                                      _result = 3u;
                                                      return {};
                                                    },
                                                    [&](const typename LoopifyLists::
                                                            list<unsigned int>::
                                                                Cons _args2)
                                                        -> unsigned int {
                                                      _stack.push_back(_Call1{
                                                          (_args.d_a0 +
                                                           _args0.d_a0),
                                                          (_args1.d_a0 +
                                                           _args2.d_a0)});
                                                      _stack.push_back(
                                                          _Enter{_args2.d_a1});
                                                      return {};
                                                    }},
                                                _args1.d_a1->v());
                                            return {};
                                          }},
                                      _args0.d_a1->v());
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + (_f._s1 + _result)); }},
        _frame);
  }
  return _result;
}

/// between lo hi l filters elements in range lo, hi.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::between(
    const unsigned int lo, const unsigned int hi,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int hi;
    const unsigned int lo;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, hi, lo});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int hi = _f.hi;
              const unsigned int lo = _f.lo;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        if ((lo <= _args.d_a0 && _args.d_a0 <= hi)) {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(
                              _Enter{_args.d_a1, std::move(hi), std::move(lo)});
                        } else {
                          _stack.push_back(
                              _Enter{_args.d_a1, std::move(hi), std::move(lo)});
                        }
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// categorize k l categorizes elements: 1 for <k, 2 for =k, 3 for >k.
__attribute__((pure)) unsigned int LoopifyLists::categorize(
    const unsigned int k,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
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
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        unsigned int score;
                        if (k < _args.d_a0) {
                          score = 3u;
                        } else {
                          if (_args.d_a0 == k) {
                            score = 2u;
                          } else {
                            score = 1u;
                          }
                        }
                        _stack.push_back(_Call1{std::move(score)});
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

/// max_prefix_sum l maximum prefix sum (Kadane-like).
__attribute__((pure)) unsigned int LoopifyLists::max_prefix_sum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
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
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int rest = _result;
              unsigned int sum = (_args.d_a0 + std::move(rest));
              if (0u <= sum) {
                _result = std::move(sum);
              } else {
                _result = 0u;
              }
            }},
        _frame);
  }
  return _result;
}

/// pairwise_sum l sums consecutive pairs: 1,2,3,4 -> 3,7.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::pairwise_sum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype((
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0 +
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _result = list<unsigned int>::ctor::Nil_();
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _stack.push_back(
                                      _Call1{(_args.d_a0 + _args0.d_a0)});
                                  _stack.push_back(_Enter{_args0.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// weighted_sum i l weighted sum with increasing weights.
__attribute__((pure)) unsigned int LoopifyLists::weighted_sum(
    const unsigned int i,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int i;
  };

  struct _Call1 {
    decltype((
        std::declval<const unsigned int &>() *
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, i});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int i = _f.i;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{(i * _args.d_a0)});
                        _stack.push_back(_Enter{_args.d_a1, (i + 1)});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// prefix_sums acc l returns all prefix sums: 1,2,3 -> 0,1,3,6.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::prefix_sums(
    const unsigned int acc,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int acc;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, acc});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int acc = _f.acc;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Cons_(
                            std::move(acc), list<unsigned int>::ctor::Nil_());
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _stack.push_back(_Call1{acc});
                        _stack.push_back(
                            _Enter{_args.d_a1, (acc + _args.d_a0)});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// uniq_sorted l removes consecutive duplicates from sorted list.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::uniq_sorted(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _result = list<unsigned int>::ctor::Cons_(
                                      _args.d_a0,
                                      list<unsigned int>::ctor::Nil_());
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
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
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// Helper: take first n elements.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::take_n(
    const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int n;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int n = _f.n;
              if (n <= 0) {
                _result = list<unsigned int>::ctor::Nil_();
              } else {
                unsigned int m = n - 1;
                std::visit(
                    Overloaded{
                        [&](const typename LoopifyLists::list<unsigned int>::Nil
                                _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<unsigned int>> {
                          _result = list<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename LoopifyLists::list<
                            unsigned int>::Cons _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<unsigned int>> {
                          _stack.push_back(_Call1{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1, m});
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// Helper: list length.
__attribute__((pure)) unsigned int LoopifyLists::len_list(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {};

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
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_result + 1); }},
        _frame);
  }
  return _result;
}

/// windows n l returns all sliding windows of size n.
std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::windows_aux(
    const unsigned int fuel, const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    std::shared_ptr<LoopifyLists::list<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<
      LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    list<std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                        ctor::Nil_();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename LoopifyLists::list<unsigned int>::Nil
                                _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<std::shared_ptr<
                                    LoopifyLists::list<unsigned int>>>> {
                          _result = list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename LoopifyLists::list<
                            unsigned int>::Cons _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<std::shared_ptr<
                                    LoopifyLists::list<unsigned int>>>> {
                          if (len_list(l) < n) {
                            _result = list<std::shared_ptr<LoopifyLists::list<
                                unsigned int>>>::ctor::Nil_();
                          } else {
                            std::shared_ptr<LoopifyLists::list<unsigned int>>
                                window = take_n(n, std::move(l));
                            std::visit(
                                Overloaded{
                                    [&](const typename LoopifyLists::list<
                                        unsigned int>::Nil _args0)
                                        -> std::shared_ptr<LoopifyLists::list<
                                            std::shared_ptr<LoopifyLists::list<
                                                unsigned int>>>> {
                                      _result = list<std::shared_ptr<
                                          LoopifyLists::list<unsigned int>>>::
                                          ctor::Nil_();
                                      return {};
                                    },
                                    [&](const typename LoopifyLists::list<
                                        unsigned int>::Cons _args0)
                                        -> std::shared_ptr<LoopifyLists::list<
                                            std::shared_ptr<LoopifyLists::list<
                                                unsigned int>>>> {
                                      _stack.push_back(
                                          _Call1{std::move(window)});
                                      _stack.push_back(_Enter{_args.d_a1, f});
                                      return {};
                                    }},
                                window->v());
                          }
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result =
                  list<std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                      ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::windows(const unsigned int n,
                      std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  return windows_aux((len_list(l) + 1), n, l);
}

/// is_prefix_of l1 l2 checks if l1 is a prefix of l2.
__attribute__((pure)) bool LoopifyLists::is_prefix_of(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l2) {
  bool _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l2 = l2;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l1 = l1;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil _args) {
              _result = true;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args0) {
                        _result = false;
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args0) {
                        if (_args.d_a0 == _args0.d_a0) {
                          std::shared_ptr<LoopifyLists::list<unsigned int>>
                              _next_l2 = _args0.d_a1;
                          std::shared_ptr<LoopifyLists::list<unsigned int>>
                              _next_l1 = _args.d_a1;
                          _loop_l2 = std::move(_next_l2);
                          _loop_l1 = std::move(_next_l1);
                        } else {
                          _result = false;
                          _continue = false;
                        }
                      }},
                  _loop_l2->v());
            }},
        _loop_l1->v());
  }
  return _result;
}

/// lookup_all key l finds all values for key in association list.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::lookup_all(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
        l;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<
                          std::pair<unsigned int, unsigned int>>::Nil _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<
                          std::pair<unsigned int, unsigned int>>::Cons _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        unsigned int k = _args.d_a0.first;
                        unsigned int v = _args.d_a0.second;
                        if (k == key) {
                          _stack.push_back(_Call1{v});
                          _stack.push_back(_Enter{_args.d_a1});
                        } else {
                          _stack.push_back(_Enter{_args.d_a1});
                        }
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// member x l checks if x is in the list.
__attribute__((pure)) bool LoopifyLists::member(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  bool _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil _args) {
              _result = false;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons _args) {
              if (x == _args.d_a0) {
                _result = true;
                _continue = false;
              } else {
                _loop_l = _args.d_a1;
              }
            }},
        _loop_l->v());
  }
  return _result;
}

/// product l multiplies all elements in the list.
__attribute__((pure)) unsigned int LoopifyLists::product(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 1u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 * _result); }},
        _frame);
  }
  return _result;
}

/// sum_list l sums all elements in the list.
__attribute__((pure)) unsigned int LoopifyLists::sum_list(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0});
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

/// flatten_nested l alternative flatten with different pattern: flattens one
/// level at a time. Pattern:  :: rest -> flatten rest, (x :: xs) :: rest -> x
/// :: flatten (xs :: rest).
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::flatten_nested_fuel(
    const unsigned int fuel,
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        l;
    const unsigned int fuel;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<
                  std::shared_ptr<LoopifyLists::list<unsigned int>>>>
                  l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = list<unsigned int>::ctor::Nil_();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename LoopifyLists::list<std::shared_ptr<
                                LoopifyLists::list<unsigned int>>>::Nil _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<unsigned int>> {
                          _result = list<unsigned int>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename LoopifyLists::list<std::shared_ptr<
                                LoopifyLists::list<unsigned int>>>::Cons _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<unsigned int>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyLists::list<
                                      unsigned int>::Nil _args0)
                                      -> std::shared_ptr<
                                          LoopifyLists::list<unsigned int>> {
                                    _stack.push_back(_Enter{_args.d_a1, f});
                                    return {};
                                  },
                                  [&](const typename LoopifyLists::list<
                                      unsigned int>::Cons _args0)
                                      -> std::shared_ptr<
                                          LoopifyLists::list<unsigned int>> {
                                    _stack.push_back(_Call1{_args0.d_a0});
                                    _stack.push_back(_Enter{
                                        list<std::shared_ptr<
                                            LoopifyLists::list<unsigned int>>>::
                                            ctor::Cons_(_args0.d_a1,
                                                        _args.d_a1),
                                        f});
                                    return {};
                                  }},
                              _args.d_a0->v());
                          return {};
                        }},
                    l->v());
              }
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyLists::sum_list_lengths(
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        l;
  };

  struct _Call1 {
    decltype(len_list(
        std::declval<const typename LoopifyLists::list<
            std::shared_ptr<LoopifyLists::list<unsigned int>>>::Cons &>()
            .d_a0)) _s0;
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
              const std::shared_ptr<LoopifyLists::list<
                  std::shared_ptr<LoopifyLists::list<unsigned int>>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Nil _args)
                          -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Cons _args)
                          -> unsigned int {
                        _stack.push_back(_Call1{len_list(_args.d_a0)});
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

std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::flatten_nested(
    std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        l) {
  return flatten_nested_fuel((sum_list_lengths(l) + 1), l);
}

/// compress l removes consecutive duplicates: 1,1,2,2,2,3 -> 1,2,3.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::compress(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _result = list<unsigned int>::ctor::Cons_(
                                      _args.d_a0,
                                      list<unsigned int>::ctor::Nil_());
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
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
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// group_pairs l groups consecutive elements into pairs: 1,2,3,4 ->
/// (1,2),(3,4).
std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
LoopifyLists::group_pairs(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0,
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<
                              std::pair<unsigned int, unsigned int>>> {
                        _result = list<std::pair<unsigned int,
                                                 unsigned int>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<
                              std::pair<unsigned int, unsigned int>>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<std::pair<
                                            unsigned int, unsigned int>>> {
                                  _result = list<
                                      std::pair<unsigned int,
                                                unsigned int>>::ctor::Nil_();
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<std::pair<
                                            unsigned int, unsigned int>>> {
                                  _stack.push_back(_Call1{
                                      std::make_pair(_args.d_a0, _args0.d_a0)});
                                  _stack.push_back(_Enter{_args0.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result =
                  list<std::pair<unsigned int, unsigned int>>::ctor::Cons_(
                      _f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// swizzle l separates elements by position: 1,2,3,4 -> (1,3,2,4).
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
          std::shared_ptr<LoopifyLists::list<unsigned int>>>
LoopifyLists::swizzle(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
            std::shared_ptr<LoopifyLists::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::pair<
                              std::shared_ptr<LoopifyLists::list<unsigned int>>,
                              std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>> {
                        _result =
                            std::make_pair(list<unsigned int>::ctor::Nil_(),
                                           list<unsigned int>::ctor::Nil_());
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::pair<
                              std::shared_ptr<LoopifyLists::list<unsigned int>>,
                              std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>> {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              std::shared_ptr<LoopifyLists::list<unsigned int>> odds =
                  _result.first;
              std::shared_ptr<LoopifyLists::list<unsigned int>> evens =
                  _result.second;
              _result = std::make_pair(
                  list<unsigned int>::ctor::Cons_(_args.d_a0, evens), odds);
            }},
        _frame);
  }
  return _result;
}

/// index_of_aux x l i finds first index of x in l starting from i.
__attribute__((pure)) unsigned int LoopifyLists::index_of_aux(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
    const unsigned int i) {
  unsigned int _result;
  unsigned int _loop_i = i;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil _args) {
              _result = 0u;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons _args) {
              if (x == _args.d_a0) {
                _result = std::move(_loop_i);
                _continue = false;
              } else {
                unsigned int _next_i = (std::move(_loop_i) + 1);
                std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                    _args.d_a1;
                _loop_i = std::move(_next_i);
                _loop_l = std::move(_next_l);
              }
            }},
        _loop_l->v());
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyLists::index_of(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  return index_of_aux(x, l, 0u);
}

/// interleave l1 l2 interleaves two lists: 1,2 3,4 -> 1,3,2,4.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::interleave(std::shared_ptr<LoopifyLists::list<unsigned int>> l1,
                         std::shared_ptr<LoopifyLists::list<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2;
    std::shared_ptr<LoopifyLists::list<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> l2 = _f.l2;
              std::shared_ptr<LoopifyLists::list<unsigned int>> l1 = _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = std::move(l2);
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _result = std::move(l1);
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _stack.push_back(
                                      _Call1{_args.d_a0, _args0.d_a0});
                                  _stack.push_back(
                                      _Enter{_args0.d_a1, _args.d_a1});
                                  return {};
                                }},
                            std::move(l2)->v());
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(
                  _f._s0, list<unsigned int>::ctor::Cons_(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

/// lookup key l finds value for key in association list.
__attribute__((pure)) unsigned int LoopifyLists::lookup(
    const unsigned int key,
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>> &l) {
  unsigned int _result;
  std::shared_ptr<LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
      _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{[&](const typename LoopifyLists::list<
                       std::pair<unsigned int, unsigned int>>::Nil _args) {
                     _result = 0u;
                     _continue = false;
                   },
                   [&](const typename LoopifyLists::list<
                       std::pair<unsigned int, unsigned int>>::Cons _args) {
                     unsigned int k = _args.d_a0.first;
                     unsigned int v = _args.d_a0.second;
                     if (k == key) {
                       _result = v;
                       _continue = false;
                     } else {
                       _loop_l = _args.d_a1;
                     }
                   }},
        _loop_l->v());
  }
  return _result;
}

/// group l groups consecutive equal elements: 1,1,2,2,2,3 -> [1,1],[2,2,2],[3].
std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::group_fuel(
    const unsigned int fuel,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int fuel;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  struct _Call2 {
    decltype(list<unsigned int>::ctor::Cons_(
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0,
        list<unsigned int>::ctor::Nil_())) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  std::shared_ptr<
      LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result =
                    list<std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                        ctor::Nil_();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename LoopifyLists::list<unsigned int>::Nil
                                _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<std::shared_ptr<
                                    LoopifyLists::list<unsigned int>>>> {
                          _result = list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::ctor::Nil_();
                          return {};
                        },
                        [&](const typename LoopifyLists::list<
                            unsigned int>::Cons _args)
                            -> std::shared_ptr<
                                LoopifyLists::list<std::shared_ptr<
                                    LoopifyLists::list<unsigned int>>>> {
                          std::visit(
                              Overloaded{
                                  [&](const typename LoopifyLists::list<
                                      unsigned int>::Nil _args0)
                                      -> std::shared_ptr<LoopifyLists::list<
                                          std::shared_ptr<LoopifyLists::list<
                                              unsigned int>>>> {
                                    _result = list<std::shared_ptr<
                                        LoopifyLists::list<unsigned int>>>::
                                        ctor::Cons_(
                                            list<unsigned int>::ctor::Cons_(
                                                _args.d_a0, list<unsigned int>::
                                                                ctor::Nil_()),
                                            list<std::shared_ptr<
                                                LoopifyLists::list<
                                                    unsigned int>>>::ctor::
                                                Nil_());
                                    return {};
                                  },
                                  [&](const typename LoopifyLists::list<
                                      unsigned int>::Cons _args0)
                                      -> std::shared_ptr<LoopifyLists::list<
                                          std::shared_ptr<LoopifyLists::list<
                                              unsigned int>>>> {
                                    if (_args.d_a0 == _args0.d_a0) {
                                      _stack.push_back(_Call1{_args});
                                      _stack.push_back(_Enter{_args.d_a1, f});
                                    } else {
                                      _stack.push_back(_Call2{
                                          list<unsigned int>::ctor::Cons_(
                                              _args.d_a0, list<unsigned int>::
                                                              ctor::Nil_())});
                                      _stack.push_back(_Enter{_args.d_a1, f});
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
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Nil _args1)
                          -> void {
                        _result = list<
                            std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                            ctor::Cons_(list<unsigned int>::ctor::Cons_(
                                            _args.d_a0,
                                            list<unsigned int>::ctor::Nil_()),
                                        list<std::shared_ptr<LoopifyLists::list<
                                            unsigned int>>>::ctor::Nil_());
                      },
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Cons _args1)
                          -> void {
                        _result = list<
                            std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                            ctor::Cons_(list<unsigned int>::ctor::Cons_(
                                            _args.d_a0, _args1.d_a0),
                                        _args1.d_a1);
                      }},
                  _result->v());
            },
            [&](_Call2 _f) {
              _result =
                  list<std::shared_ptr<LoopifyLists::list<unsigned int>>>::
                      ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<
    LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
LoopifyLists::group(std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  return group_fuel((len_list(l) + 1), l);
}

/// Internal helper: reverse a list.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::rev_helper(
    std::shared_ptr<LoopifyLists::list<unsigned int>> acc,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_acc = acc;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil _args) {
              _result = std::move(_loop_acc);
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons _args) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                  _args.d_a1;
              std::shared_ptr<LoopifyLists::list<unsigned int>> _next_acc =
                  list<unsigned int>::ctor::Cons_(_args.d_a0,
                                                  std::move(_loop_acc));
              _loop_l = std::move(_next_l);
              _loop_acc = std::move(_next_acc);
            }},
        _loop_l->v());
  }
  return _result;
}

/// reverse_insert x l inserts x and reverses at each step.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::reverse_insert(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int x;
  };

  struct _Call1 {
    decltype(list<unsigned int>::ctor::Nil_()) _s0;
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, x});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int x = _f.x;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Cons_(
                            std::move(x), list<unsigned int>::ctor::Nil_());
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _stack.push_back(_Call1{
                            list<unsigned int>::ctor::Nil_(), _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1, std::move(x)});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = rev_helper(
                  _f._s0, list<unsigned int>::ctor::Cons_(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

/// Internal helper: append lists.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::app_helper(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2;
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l1 =
                  _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = std::move(l2);
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// double_append l1 l2 appends with doubling: 1,2 3 -> 1,3,3,3,3.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::double_append(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2) {
  struct _Enter {
    std::shared_ptr<LoopifyLists::list<unsigned int>> l2;
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l1;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l1 =
                  _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = std::move(l2);
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{std::move(l2), _args.d_a1});
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              std::shared_ptr<LoopifyLists::list<unsigned int>> rest = _result;
              _result = list<unsigned int>::ctor::Cons_(_args.d_a0,
                                                        app_helper(rest, rest));
            }},
        _frame);
  }
  return _result;
}

/// remove_if_sum_even l removes element if sum with next is even.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::remove_if_sum_even(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _result = list<unsigned int>::ctor::Cons_(
                                      _args.d_a0,
                                      list<unsigned int>::ctor::Nil_());
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  if (((_args.d_a0 + _args0.d_a0) % 2u) == 0u) {
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
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// split_at n l splits list at index n into (prefix, suffix).
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
          std::shared_ptr<LoopifyLists::list<unsigned int>>>
LoopifyLists::split_at(const unsigned int n,
                       std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int n;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
            std::shared_ptr<LoopifyLists::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int n = _f.n;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::pair<
                              std::shared_ptr<LoopifyLists::list<unsigned int>>,
                              std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>> {
                        _result =
                            std::make_pair(list<unsigned int>::ctor::Nil_(),
                                           list<unsigned int>::ctor::Nil_());
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::pair<
                              std::shared_ptr<LoopifyLists::list<unsigned int>>,
                              std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>> {
                        if (n == 0u) {
                          _result = std::make_pair(
                              list<unsigned int>::ctor::Nil_(), std::move(l));
                        } else {
                          _stack.push_back(_Call1{_args});
                          _stack.push_back(_Enter{
                              _args.d_a1, (((n - 1u) > n ? 0 : (n - 1u)))});
                        }
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              std::shared_ptr<LoopifyLists::list<unsigned int>> a =
                  _result.first;
              std::shared_ptr<LoopifyLists::list<unsigned int>> b =
                  _result.second;
              _result = std::make_pair(
                  list<unsigned int>::ctor::Cons_(_args.d_a0, a), b);
            }},
        _frame);
  }
  return _result;
}

/// unzip l splits list of pairs into two lists.
__attribute__((pure))
std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
          std::shared_ptr<LoopifyLists::list<unsigned int>>>
LoopifyLists::unzip(
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>> &l) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
        l;
  };

  struct _Call1 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::shared_ptr<LoopifyLists::list<unsigned int>>,
            std::shared_ptr<LoopifyLists::list<unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<
                  LoopifyLists::list<std::pair<unsigned int, unsigned int>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<
                          std::pair<unsigned int, unsigned int>>::Nil _args)
                          -> std::pair<
                              std::shared_ptr<LoopifyLists::list<unsigned int>>,
                              std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>> {
                        _result =
                            std::make_pair(list<unsigned int>::ctor::Nil_(),
                                           list<unsigned int>::ctor::Nil_());
                        return {};
                      },
                      [&](const typename LoopifyLists::list<
                          std::pair<unsigned int, unsigned int>>::Cons _args)
                          -> std::pair<
                              std::shared_ptr<LoopifyLists::list<unsigned int>>,
                              std::shared_ptr<
                                  LoopifyLists::list<unsigned int>>> {
                        unsigned int a = _args.d_a0.first;
                        unsigned int b = _args.d_a0.second;
                        _stack.push_back(_Call1{b, a});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              unsigned int b = _f._s0;
              unsigned int a = _f._s1;
              std::shared_ptr<LoopifyLists::list<unsigned int>> xs =
                  _result.first;
              std::shared_ptr<LoopifyLists::list<unsigned int>> ys =
                  _result.second;
              _result = std::make_pair(list<unsigned int>::ctor::Cons_(a, xs),
                                       list<unsigned int>::ctor::Cons_(b, ys));
            }},
        _frame);
  }
  return _result;
}

/// nth n l default returns nth element or default if out of bounds.
__attribute__((pure)) unsigned int
LoopifyLists::nth(const unsigned int n,
                  const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
                  const unsigned int default0) {
  unsigned int _result;
  unsigned int _loop_default0 = default0;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil _args) {
              _result = std::move(_loop_default0);
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons _args) {
              if (_loop_n == 0u) {
                _result = _args.d_a0;
                _continue = false;
              } else {
                unsigned int _next_default0 = std::move(_loop_default0);
                std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                    _args.d_a1;
                unsigned int _next_n =
                    (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                _loop_default0 = std::move(_next_default0);
                _loop_l = std::move(_next_l);
                _loop_n = std::move(_next_n);
              }
            }},
        _loop_l->v());
  }
  return _result;
}

/// last l default returns last element or default if empty.
__attribute__((pure)) unsigned int
LoopifyLists::last(const std::shared_ptr<LoopifyLists::list<unsigned int>> &l,
                   const unsigned int default0) {
  unsigned int _result;
  unsigned int _loop_default0 = default0;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil _args) {
              _result = std::move(_loop_default0);
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons _args) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args0) {
                        _result = _args.d_a0;
                        _continue = false;
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args0) {
                        unsigned int _next_default0 = std::move(_loop_default0);
                        std::shared_ptr<LoopifyLists::list<unsigned int>>
                            _next_l = _args.d_a1;
                        _loop_default0 = std::move(_next_default0);
                        _loop_l = std::move(_next_l);
                      }},
                  _args.d_a1->v());
            }},
        _loop_l->v());
  }
  return _result;
}

/// drop n l drops first n elements.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::drop(const unsigned int n,
                   std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  struct _Enter {
    std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int n;
  };

  using _Frame = std::variant<_Enter>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
          std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
          const unsigned int n = _f.n;
          if (l.use_count() == 1 && l->v().index() == 0) {
            auto &_rf = std::get<0>(l->v_mut());
            _result = l;
          } else {
            std::visit(
                Overloaded{
                    [&](const typename LoopifyLists::list<unsigned int>::Nil
                            _args)
                        -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                      _result = list<unsigned int>::ctor::Nil_();
                      return {};
                    },
                    [&](const typename LoopifyLists::list<unsigned int>::Cons
                            _args)
                        -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                      if (n == 0u) {
                        _result = std::move(l);
                      } else {
                        _stack.push_back(_Enter{
                            _args.d_a1, (((n - 1u) > n ? 0 : (n - 1u)))});
                      }
                      return {};
                    }},
                l->v());
          }
        }},
        _frame);
  }
  return _result;
}

/// init l returns all but last element.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::init(const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyLists::list<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _result = list<unsigned int>::ctor::Nil_();
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _stack.push_back(_Call1{_args.d_a0});
                                  _stack.push_back(_Enter{_args.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              _result = list<unsigned int>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// count x l counts occurrences of x in l.
__attribute__((pure)) unsigned int LoopifyLists::count(
    const unsigned int x,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
    const unsigned int x;
  };

  struct _Call1 {};

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l, x});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              const unsigned int x = _f.x;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        if (x == _args.d_a0) {
                          _stack.push_back(_Call1{});
                          _stack.push_back(_Enter{_args.d_a1, std::move(x)});
                        } else {
                          _stack.push_back(_Enter{_args.d_a1, std::move(x)});
                        }
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_result + 1); }},
        _frame);
  }
  return _result;
}

/// maximum l finds maximum element (returns 0 for empty list).
__attribute__((pure)) unsigned int LoopifyLists::maximum(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
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
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> unsigned int {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0) -> unsigned int {
                                  _result = _args.d_a0;
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> unsigned int {
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
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int max_rest = _result;
              if (max_rest <= _args.d_a0) {
                _result = _args.d_a0;
              } else {
                _result = std::move(max_rest);
              }
            }},
        _frame);
  }
  return _result;
}

/// minmax l finds both minimum and maximum in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::minmax(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> std::pair<unsigned int, unsigned int> {
                        _result = std::make_pair(0u, 0u);
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> std::pair<unsigned int, unsigned int> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::pair<unsigned int, unsigned int> {
                                  _result =
                                      std::make_pair(_args.d_a0, _args.d_a0);
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::pair<unsigned int, unsigned int> {
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
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int lo = _result.first;
              unsigned int hi = _result.second;
              _result = std::make_pair(
                  [&](void) {
                    if (_args.d_a0 <= lo) {
                      return _args.d_a0;
                    } else {
                      return lo;
                    }
                  }(),
                  [&](void) {
                    if (hi <= _args.d_a0) {
                      return _args.d_a0;
                    } else {
                      return hi;
                    }
                  }());
            }},
        _frame);
  }
  return _result;
}

/// Helper for rotate_left.
std::shared_ptr<LoopifyLists::list<unsigned int>>
LoopifyLists::rotate_left_fuel(
    const unsigned int fuel, const unsigned int n,
    std::shared_ptr<LoopifyLists::list<unsigned int>> l) {
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
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
      unsigned int f = _loop_fuel - 1;
      if (_loop_n == 0u) {
        {
          _result = _loop_l;
          _continue = false;
        }
      } else {
        std::visit(
            Overloaded{
                [&](const typename LoopifyLists::list<unsigned int>::Nil
                        _args) {
                  _result = list<unsigned int>::ctor::Nil_();
                  _continue = false;
                },
                [&](const typename LoopifyLists::list<unsigned int>::Cons
                        _args) {
                  std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                      app_helper(
                          _args.d_a1,
                          list<unsigned int>::ctor::Cons_(
                              _args.d_a0, list<unsigned int>::ctor::Nil_()));
                  unsigned int _next_n =
                      (((_loop_n - 1u) > _loop_n ? 0 : (_loop_n - 1u)));
                  unsigned int _next_fuel = std::move(f);
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

/// rotate_left n l rotates list left by n positions: rotate 2 1,2,3,4 ->
/// 3,4,1,2.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::rotate_left(
    const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  return rotate_left_fuel((n + 1), n, l);
}

/// intercalate sep lists joins lists with separator: intercalate 0 [1,2],[3,4]
/// -> 1,2,0,3,4.
std::shared_ptr<LoopifyLists::list<unsigned int>> LoopifyLists::intercalate(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &sep,
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        &lists) {
  struct _Enter {
    const std::shared_ptr<
        LoopifyLists::list<std::shared_ptr<LoopifyLists::list<unsigned int>>>>
        lists;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyLists::list<
                 std::shared_ptr<LoopifyLists::list<unsigned int>>>::Cons &>()
                 .d_a0) _s0;
    const std::shared_ptr<LoopifyLists::list<unsigned int>> _s1;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{lists});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<
                  std::shared_ptr<LoopifyLists::list<unsigned int>>>>
                  lists = _f.lists;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Nil _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        _result = list<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<std::shared_ptr<
                              LoopifyLists::list<unsigned int>>>::Cons _args)
                          -> std::shared_ptr<LoopifyLists::list<unsigned int>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    std::shared_ptr<LoopifyLists::list<
                                        unsigned int>>>::Nil _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _result = _args.d_a0;
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    std::shared_ptr<LoopifyLists::list<
                                        unsigned int>>>::Cons _args0)
                                    -> std::shared_ptr<
                                        LoopifyLists::list<unsigned int>> {
                                  _stack.push_back(_Call1{_args.d_a0, sep});
                                  _stack.push_back(_Enter{_args.d_a1});
                                  return {};
                                }},
                            _args.d_a1->v());
                        return {};
                      }},
                  lists->v());
            },
            [&](_Call1 _f) {
              _result = app_helper(_f._s0, app_helper(_f._s1, _result));
            }},
        _frame);
  }
  return _result;
}

/// majority l finds majority element using Boyer-Moore voting algorithm.
/// Returns (candidate, count).
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::majority(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> std::pair<unsigned int, unsigned int> {
                        _result = std::make_pair(0u, 0u);
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> std::pair<unsigned int, unsigned int> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::pair<unsigned int, unsigned int> {
                                  _result = std::make_pair(_args.d_a0, 1u);
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::pair<unsigned int, unsigned int> {
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
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int cand = _result.first;
              unsigned int cnt = _result.second;
              if (_args.d_a0 == cand) {
                _result = std::make_pair(cand, (cnt + 1));
              } else {
                if (cnt == 0u) {
                  _result = std::make_pair(_args.d_a0, 1u);
                } else {
                  _result = std::make_pair(
                      cand, (((cnt - 1u) > cnt ? 0 : (cnt - 1u))));
                }
              }
            }},
        _frame);
  }
  return _result;
}

/// zip3 l1 l2 l3 zips three lists into triples.
std::shared_ptr<LoopifyLists::list<
    std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
LoopifyLists::zip3(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l1,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l2,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l3) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l3;
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l2;
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l1;
  };

  struct _Call1 {
    decltype(std::make_pair(
        std::make_pair(
            std::declval<
                const typename LoopifyLists::list<unsigned int>::Cons &>()
                .d_a0,
            std::declval<
                const typename LoopifyLists::list<unsigned int>::Cons &>()
                .d_a0),
        std::declval<const typename LoopifyLists::list<unsigned int>::Cons &>()
            .d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<LoopifyLists::list<
      std::pair<std::pair<unsigned int, unsigned int>, unsigned int>>>
      _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l3, l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l3 =
                  _f.l3;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l2 =
                  _f.l2;
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l1 =
                  _f.l1;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>> {
                        _result = list<
                            std::pair<std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args)
                          -> std::shared_ptr<LoopifyLists::list<
                              std::pair<std::pair<unsigned int, unsigned int>,
                                        unsigned int>>> {
                        std::visit(
                            Overloaded{
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Nil _args0)
                                    -> std::shared_ptr<LoopifyLists::list<
                                        std::pair<std::pair<unsigned int,
                                                            unsigned int>,
                                                  unsigned int>>> {
                                  _result = list<std::pair<
                                      std::pair<unsigned int, unsigned int>,
                                      unsigned int>>::ctor::Nil_();
                                  return {};
                                },
                                [&](const typename LoopifyLists::list<
                                    unsigned int>::Cons _args0)
                                    -> std::shared_ptr<LoopifyLists::list<
                                        std::pair<std::pair<unsigned int,
                                                            unsigned int>,
                                                  unsigned int>>> {
                                  std::visit(
                                      Overloaded{
                                          [&](const typename LoopifyLists::list<
                                              unsigned int>::Nil _args1)
                                              -> std::shared_ptr<
                                                  LoopifyLists::list<std::pair<
                                                      std::pair<unsigned int,
                                                                unsigned int>,
                                                      unsigned int>>> {
                                            _result = list<std::pair<
                                                std::pair<unsigned int,
                                                          unsigned int>,
                                                unsigned int>>::ctor::Nil_();
                                            return {};
                                          },
                                          [&](const typename LoopifyLists::list<
                                              unsigned int>::Cons _args1)
                                              -> std::shared_ptr<
                                                  LoopifyLists::list<std::pair<
                                                      std::pair<unsigned int,
                                                                unsigned int>,
                                                      unsigned int>>> {
                                            _stack.push_back(
                                                _Call1{std::make_pair(
                                                    std::make_pair(_args.d_a0,
                                                                   _args0.d_a0),
                                                    _args1.d_a0)});
                                            _stack.push_back(
                                                _Enter{_args1.d_a1, _args0.d_a1,
                                                       _args.d_a1});
                                            return {};
                                          }},
                                      l3->v());
                                  return {};
                                }},
                            l2->v());
                        return {};
                      }},
                  l1->v());
            },
            [&](_Call1 _f) {
              _result =
                  list<std::pair<std::pair<unsigned int, unsigned int>,
                                 unsigned int>>::ctor::Cons_(_f._s0, _result);
            }},
        _frame);
  }
  return _result;
}

/// sum_and_count l returns both sum and count in one pass.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
LoopifyLists::sum_and_count(
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<LoopifyLists::list<unsigned int>> l;
  };

  struct _Call1 {
    const typename LoopifyLists::list<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<unsigned int, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyLists::list<unsigned int>> l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyLists::list<unsigned int>::Nil
                              _args) -> std::pair<unsigned int, unsigned int> {
                        _result = std::make_pair(0u, 0u);
                        return {};
                      },
                      [&](const typename LoopifyLists::list<unsigned int>::Cons
                              _args) -> std::pair<unsigned int, unsigned int> {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyLists::list<unsigned int>::Cons _args =
                  _f._s0;
              unsigned int s = _result.first;
              unsigned int c = _result.second;
              _result = std::make_pair((_args.d_a0 + s), (c + 1));
            }},
        _frame);
  }
  return _result;
}

/// elem_at n l returns element at index n (like nth but with different name).
__attribute__((pure)) std::optional<unsigned int> LoopifyLists::elem_at(
    const unsigned int n,
    const std::shared_ptr<LoopifyLists::list<unsigned int>> &l) {
  std::optional<unsigned int> _result;
  std::shared_ptr<LoopifyLists::list<unsigned int>> _loop_l = l;
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    std::visit(
        Overloaded{
            [&](const typename LoopifyLists::list<unsigned int>::Nil _args) {
              _result = std::nullopt;
              _continue = false;
            },
            [&](const typename LoopifyLists::list<unsigned int>::Cons _args) {
              if (_loop_n == 0u) {
                _result = std::make_optional<unsigned int>(_args.d_a0);
                _continue = false;
              } else {
                std::shared_ptr<LoopifyLists::list<unsigned int>> _next_l =
                    _args.d_a1;
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
