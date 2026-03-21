#include <loopify_generators.h>

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

/// Consolidated list generator functions.
/// cycle n l repeats the list n times: cycle 2 1,2 -> 1,2,1,2.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::cycle(const unsigned int n,
                         const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{l});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) { _result = _f._s0->app(_result); }},
               _frame);
  }
  return _result;
}

/// zip_longest l1 l2 default zips, using default for missing elements.
std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyGenerators::zip_longest_aux(
    const std::shared_ptr<List<unsigned int>> &l1,
    const std::shared_ptr<List<unsigned int>> &l2, const unsigned int default0,
    const unsigned int fuel) {
  struct _Enter {
    const unsigned int fuel;
    const std::shared_ptr<List<unsigned int>> l2;
    const std::shared_ptr<List<unsigned int>> l1;
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
  _stack.push_back(_Enter{fuel, l2, l1});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int fuel = _f.fuel;
              const std::shared_ptr<List<unsigned int>> l2 = _f.l2;
              const std::shared_ptr<List<unsigned int>> l1 = _f.l1;
              if (fuel <= 0) {
                _result =
                    List<std::pair<unsigned int, unsigned int>>::ctor::Nil_();
              } else {
                unsigned int f = fuel - 1;
                std::visit(
                    Overloaded{
                        [&](const typename List<unsigned int>::Nil _args)
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
                                    _stack.push_back(_Call1{
                                        std::make_pair(default0, _args0.d_a0)});
                                    _stack.push_back(_Enter{
                                        f, _args0.d_a1,
                                        List<unsigned int>::ctor::Nil_()});
                                    return {};
                                  }},
                              l2->v());
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
                                    _stack.push_back(_Call2{
                                        std::make_pair(_args.d_a0, default0)});
                                    _stack.push_back(_Enter{
                                        f, List<unsigned int>::ctor::Nil_(),
                                        _args.d_a1});
                                    return {};
                                  },
                                  [&](const typename List<unsigned int>::Cons
                                          _args0)
                                      -> std::shared_ptr<List<std::pair<
                                          unsigned int, unsigned int>>> {
                                    _stack.push_back(_Call3{std::make_pair(
                                        _args.d_a0, _args0.d_a0)});
                                    _stack.push_back(
                                        _Enter{f, _args0.d_a1, _args.d_a1});
                                    return {};
                                  }},
                              l2->v());
                          return {};
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

__attribute__((pure)) unsigned int
LoopifyGenerators::len_impl(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
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

std::shared_ptr<List<std::pair<unsigned int, unsigned int>>>
LoopifyGenerators::zip_longest(const std::shared_ptr<List<unsigned int>> &l1,
                               const std::shared_ptr<List<unsigned int>> &l2,
                               const unsigned int default0) {
  return zip_longest_aux(l1, l2, default0, (len_impl(l1) + len_impl(l2)));
}

/// build_list n builds tree-like list structure: build_list(4) -> 2,4,2.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::build_list_fuel(const unsigned int fuel,
                                   const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{[&](_Enter _f) {
                     const unsigned int n = _f.n;
                     const unsigned int fuel = _f.fuel;
                     if (fuel <= 0) {
                       _result = List<unsigned int>::ctor::Nil_();
                     } else {
                       unsigned int f = fuel - 1;
                       if (n <= 0) {
                         _result = List<unsigned int>::ctor::Nil_();
                       } else {
                         unsigned int n_ = n - 1;
                         if (n_ <= 0) {
                           _result = List<unsigned int>::ctor::Cons_(
                               1u, List<unsigned int>::ctor::Nil_());
                         } else {
                           unsigned int _x = n_ - 1;
                           unsigned int half = Nat::div(n_, 2u);
                           _stack.push_back(_Call1{n_});
                           _stack.push_back(_Enter{std::move(half), f});
                         }
                       }
                     }
                   },
                   [&](_Call1 _f) {
                     unsigned int n_ = _f._s0;
                     std::shared_ptr<List<unsigned int>> half_result = _result;
                     _result = half_result->app(
                         List<unsigned int>::ctor::Cons_(n_, half_result));
                   }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>>
LoopifyGenerators::build_list(const unsigned int n) {
  return build_list_fuel(100u, n);
}

/// take n l returns first n elements.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::take(const unsigned int n,
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
        Overloaded{[&](_Enter _f) {
                     const std::shared_ptr<List<unsigned int>> l = _f.l;
                     const unsigned int n = _f.n;
                     std::visit(
                         Overloaded{
                             [&](const typename List<unsigned int>::Nil _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               _result = List<unsigned int>::ctor::Nil_();
                               return {};
                             },
                             [&](const typename List<unsigned int>::Cons _args)
                                 -> std::shared_ptr<List<unsigned int>> {
                               if (n == 0u) {
                                 _result = List<unsigned int>::ctor::Nil_();
                               } else {
                                 _stack.push_back(_Call1{_args.d_a0});
                                 _stack.push_back(
                                     _Enter{_args.d_a1,
                                            (((std::move(n) - 1u) > std::move(n)
                                                  ? 0
                                                  : (std::move(n) - 1u)))});
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

/// repeat x n creates list with n copies of x.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::repeat(const unsigned int x, const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{x});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}

/// Helper: replicate single element n times.
std::shared_ptr<List<unsigned int>>
LoopifyGenerators::replicate_single(const unsigned int x,
                                    const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    const unsigned int _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = List<unsigned int>::ctor::Nil_();
                            } else {
                              unsigned int m = n - 1;
                              _stack.push_back(_Call1{x});
                              _stack.push_back(_Enter{m});
                            }
                          },
                          [&](_Call1 _f) {
                            _result = List<unsigned int>::ctor::Cons_(_f._s0,
                                                                      _result);
                          }},
               _frame);
  }
  return _result;
}

/// replicate_each n l replicates each element n times: replicate_each 2 1,2 ->
/// 1,1,2,2.
std::shared_ptr<List<unsigned int>> LoopifyGenerators::replicate_each(
    const unsigned int n, const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(replicate_single(
        std::declval<const typename List<unsigned int>::Cons &>().d_a0,
        std::declval<const unsigned int &>())) _s0;
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
                               _stack.push_back(
                                   _Call1{replicate_single(_args.d_a0, n)});
                               _stack.push_back(_Enter{_args.d_a1});
                               return {};
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = _f._s0->app(_result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  std::pair<unsigned int, unsigned int> _result;
  unsigned int _loop_u = u;
  unsigned int _loop_q = q;
  unsigned int _loop_x = x;
  bool _continue = true;
  while (_continue) {
    if (_loop_x <= 0) {
      {
        _result = std::make_pair(std::move(_loop_q), std::move(_loop_u));
        _continue = false;
      }
    } else {
      unsigned int x_ = _loop_x - 1;
      if (_loop_u <= 0) {
        {
          unsigned int _next_u = y;
          unsigned int _next_q = (_loop_q + 1);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_q = std::move(_next_q);
          _loop_x = std::move(_next_x);
          continue;
        }
      } else {
        unsigned int u_ = _loop_u - 1;
        {
          unsigned int _next_u = std::move(u_);
          unsigned int _next_x = std::move(x_);
          _loop_u = std::move(_next_u);
          _loop_x = std::move(_next_x);
          continue;
        }
      }
    }
  }
  return _result;
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
