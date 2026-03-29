#include <loopify_multi_recursion.h>

#include <algorithm>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::mixed_arith_fuel(const unsigned int fuel,
                                        const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _Call1 {
    const unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
    const unsigned int _s3;
  };

  struct _Call2 {
    unsigned int _s0;
    const unsigned int _s1;
    const unsigned int _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
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
                       _result = 1u;
                     } else {
                       unsigned int fuel_ = fuel - 1;
                       if (n <= 0u) {
                         _result = 1u;
                       } else {
                         if (n == 1u) {
                           _result = 1u;
                         } else {
                           if (n == 2u) {
                             _result = 1u;
                           } else {
                             _stack.push_back(_Call1{
                                 (((n - 2u) > n ? 0 : (n - 2u))), fuel_,
                                 (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                             _stack.push_back(_Enter{
                                 (((n - 3u) > n ? 0 : (n - 3u))), fuel_});
                           }
                         }
                       }
                     }
                   },
                   [&](_Call1 _f) {
                     _stack.push_back(_Call2{_result, _f._s2, _f._s3});
                     _stack.push_back(_Enter{_f._s0, _f._s1});
                   },
                   [&](_Call2 _f) {
                     _stack.push_back(_Call3{_f._s0, _result});
                     _stack.push_back(_Enter{_f._s1, _f._s2});
                   },
                   [&](_Call3 _f) { _result = ((_result * _f._s1) + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::mixed_arith(const unsigned int n) {
  return mixed_arith_fuel((n * 3u), n);
}

__attribute__((pure)) bool LoopifyMultiRecursion::bool_or_chain_fuel(
    const unsigned int fuel, const unsigned int n, const unsigned int target) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
  };

  struct _Combine {
    bool _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(Overloaded{[&](_Enter _f) {
                            const unsigned int n = _f.n;
                            const unsigned int fuel = _f.fuel;
                            if (fuel <= 0) {
                              _result = false;
                            } else {
                              unsigned int fuel_ = fuel - 1;
                              if (n <= 0u) {
                                _result = false;
                              } else {
                                _stack.push_back(_After{
                                    (((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                                _stack.push_back(_Enter{
                                    (((n - 2u) > n ? 0 : (n - 2u))), fuel_});
                              }
                            }
                          },
                          [&](_After _f) {
                            _stack.push_back(_Combine{_result});
                            _stack.push_back(_Enter{_f._a0, _f._a1});
                          },
                          [&](_Combine _f) { _result = _f._left + _result; }},
               _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::bool_or_chain(const unsigned int n,
                                     const unsigned int target) {
  if (bool_or_chain_fuel((n * 2u), n, target)) {
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) bool
LoopifyMultiRecursion::bool_and_chain_fuel(const unsigned int fuel,
                                           const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
  };

  struct _Combine {
    bool _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  bool _result{};
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
                       _result = true;
                     } else {
                       unsigned int fuel_ = fuel - 1;
                       if (n <= 2u) {
                         _result = true;
                       } else {
                         _stack.push_back(
                             _After{(((n - 1u) > n ? 0 : (n - 1u))), fuel_});
                         _stack.push_back(
                             _Enter{(((n - 2u) > n ? 0 : (n - 2u))), fuel_});
                       }
                     }
                   },
                   [&](_After _f) {
                     _stack.push_back(_Combine{_result});
                     _stack.push_back(_Enter{_f._a0, _f._a1});
                   },
                   [&](_Combine _f) { _result = (_result && _f._left); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::bool_and_chain(const unsigned int n) {
  if (bool_and_chain_fuel((n * 2u), n)) {
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int LoopifyMultiRecursion::quad_count_leaves(
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> t;
  };

  struct _Call1 {
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s0;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s1;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s2;
  };

  struct _Call2 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s1;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s2;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s2;
  };

  struct _Call4 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMultiRecursion::quadtree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMultiRecursion::quadtree::QLeaf
                              _args) -> void { _result = 1u; },
                      [&](const typename LoopifyMultiRecursion::quadtree::QQuad
                              _args) -> void {
                        _stack.push_back(
                            _Call1{_args.d_a2, _args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a3});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1, _f._s2});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_f._s0, _result, _f._s2});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_f._s0, _f._s1, _result});
              _stack.push_back(_Enter{_f._s2});
            },
            [&](_Call4 _f) {
              _result = (((_result + _f._s2) + _f._s1) + _f._s0);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyMultiRecursion::quad_depth(
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> &t) {
  struct _Enter {
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> t;
  };

  struct _Call1 {
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s0;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s1;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s2;
    decltype(1u) _s3;
  };

  struct _Call2 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s1;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s2;
    decltype(1u) _s3;
  };

  struct _Call3 {
    unsigned int _s0;
    unsigned int _s1;
    const std::shared_ptr<LoopifyMultiRecursion::quadtree> _s2;
    decltype(1u) _s3;
  };

  struct _Call4 {
    unsigned int _s0;
    unsigned int _s1;
    unsigned int _s2;
    decltype(1u) _s3;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{t});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyMultiRecursion::quadtree> t = _f.t;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyMultiRecursion::quadtree::QLeaf
                              _args) -> void { _result = 0u; },
                      [&](const typename LoopifyMultiRecursion::quadtree::QQuad
                              _args) -> void {
                        _stack.push_back(
                            _Call1{_args.d_a2, _args.d_a1, _args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a3});
                      }},
                  t->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1, _f._s2, _f._s3});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_f._s0, _result, _f._s2, _f._s3});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_f._s0, _f._s1, _result, _f._s3});
              _stack.push_back(_Enter{_f._s2});
            },
            [&](_Call4 _f) {
              _result = (_f._s3 + std::max(std::max(_result, _f._s2),
                                           std::max(_f._s1, _f._s0)));
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::hofstadter_q_fuel(const unsigned int fuel,
                                         const unsigned int n) {
  struct _Enter {
    const unsigned int n;
    const unsigned int fuel;
  };

  struct _After {
    const unsigned int _a0;
    const unsigned int _a1;
  };

  struct _Combine {
    unsigned int _left;
  };

  using _Frame = std::variant<_Enter, _After, _Combine>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{n, fuel});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const unsigned int n = _f.n;
              const unsigned int fuel = _f.fuel;
              if (fuel <= 0) {
                _result = 1u;
              } else {
                unsigned int fuel_ = fuel - 1;
                if (n <= 0u) {
                  _result = 0u;
                } else {
                  if (n == 1u) {
                    _result = 1u;
                  } else {
                    if (n == 2u) {
                      _result = 1u;
                    } else {
                      unsigned int q1 = hofstadter_q_fuel(
                          fuel_, (((n - 1u) > n ? 0 : (n - 1u))));
                      unsigned int q2 = hofstadter_q_fuel(
                          fuel_, (((n - 2u) > n ? 0 : (n - 2u))));
                      _stack.push_back(_After{
                          (((n - std::move(q1)) > n ? 0 : (n - std::move(q1)))),
                          fuel_});
                      _stack.push_back(_Enter{
                          (((n - std::move(q2)) > n ? 0 : (n - std::move(q2)))),
                          fuel_});
                    }
                  }
                }
              }
            },
            [&](_After _f) {
              _stack.push_back(_Combine{_result});
              _stack.push_back(_Enter{_f._a0, _f._a1});
            },
            [&](_Combine _f) { _result = (_result + _f._left); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int
LoopifyMultiRecursion::hofstadter_q(const unsigned int n) {
  return hofstadter_q_fuel(((n * n) + 1u), n);
}
