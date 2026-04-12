#include <loopify_numeric_misc.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LoopifyNumericMisc::sum_abs(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
                               _stack.emplace_back(_Call1{_args.d_a0});
                               _stack.emplace_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::alternating_ops(const unsigned int n) {
  struct _Enter {
    const unsigned int n;
  };

  struct _Call1 {
    decltype((std::declval<unsigned int &>() + 1)) _s0;
  };

  struct _Call2 {
    decltype(((std::declval<unsigned int &>() + 1) * 2u)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.emplace_back(_Enter{n});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            if (n <= 0) {
                              _result = 0u;
                            } else {
                              unsigned int n_ = n - 1;
                              if ((2u ? (n_ + 1) % 2u : (n_ + 1)) == 0u) {
                                _stack.emplace_back(_Call1{(n_ + 1)});
                                _stack.emplace_back(_Enter{n_});
                              } else {
                                _stack.emplace_back(_Call2{((n_ + 1) * 2u)});
                                _stack.emplace_back(_Enter{n_});
                              }
                            }
                          },
                          [&](_Call1 _f) { _result = (_f._s0 + _result); },
                          [&](_Call2 _f) { _result = (_f._s0 + _result); }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::count_even(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
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
                               if ((2u ? _args.d_a0 % 2u : _args.d_a0) == 0u) {
                                 _stack.emplace_back(_Call1{1u});
                                 _stack.emplace_back(_Enter{_args.d_a1});
                               } else {
                                 _stack.emplace_back(_Enter{_args.d_a1});
                               }
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::count_odd(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(1u) _s0;
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
                               if ((2u ? _args.d_a0 % 2u : _args.d_a0) == 1u) {
                                 _stack.emplace_back(_Call1{1u});
                                 _stack.emplace_back(_Enter{_args.d_a1});
                               } else {
                                 _stack.emplace_back(_Enter{_args.d_a1});
                               }
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::product(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
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
                                 -> void { _result = 1u; },
                             [&](const typename List<unsigned int>::Cons &_args)
                                 -> void {
                               _stack.emplace_back(_Call1{_args.d_a0});
                               _stack.emplace_back(_Enter{_args.d_a1});
                             }},
                         l->v());
                   },
                   [&](_Call1 _f) { _result = (_f._s0 * _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyNumericMisc::sum_of_squares(
    const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype((
        std::declval<const typename List<unsigned int>::Cons &>().d_a0 *
        std::declval<const typename List<unsigned int>::Cons &>().d_a0)) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                        _result = 0u;
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        _stack.emplace_back(_Call1{(_args.d_a0 * _args.d_a0)});
                        _stack.emplace_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::max_two(const unsigned int a, const unsigned int b) {
  if (a < b) {
    return b;
  } else {
    return a;
  }
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::list_max(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    decltype(std::declval<const typename List<unsigned int>::Cons &>()
                 .d_a0) _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                        _result = 0u;
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &)
                                    -> void { _result = _args.d_a0; },
                                [&](const typename List<unsigned int>::Cons &)
                                    -> void {
                                  _stack.emplace_back(_Call1{_args.d_a0});
                                  _stack.emplace_back(_Enter{_args.d_a1});
                                }},
                            _args.d_a1->v());
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = max_two(_f._s0, _result); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyNumericMisc::list_min(const std::shared_ptr<List<unsigned int>> &l) {
  struct _Enter {
    const std::shared_ptr<List<unsigned int>> l;
  };

  struct _Call1 {
    const typename List<unsigned int>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  unsigned int _result{};
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
                        _result = 0u;
                      },
                      [&](const typename List<unsigned int>::Cons &_args)
                          -> void {
                        std::visit(
                            Overloaded{
                                [&](const typename List<unsigned int>::Nil &)
                                    -> void { _result = _args.d_a0; },
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
              unsigned int min_rest = _result;
              if (_args.d_a0 < min_rest) {
                _result = _args.d_a0;
              } else {
                _result = min_rest;
              }
            }},
        _frame);
  }
  return _result;
}
