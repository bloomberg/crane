#include <loopify_expr.h>

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

/// eval e evaluates an expression. Multi-constructor recursion.
__attribute__((pure)) unsigned int
LoopifyExpr::eval(const std::shared_ptr<LoopifyExpr::expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::expr> e;
  };

  struct _Call1 {};

  struct _Call2 {
    decltype(std::declval<const typename LoopifyExpr::expr::Add &>().d_a0) _s0;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  struct _Call4 {
    decltype(std::declval<const typename LoopifyExpr::expr::Mul &>().d_a0) _s0;
  };

  struct _Call5 {
    unsigned int _s0;
  };

  struct _Call6 {
    const typename LoopifyExpr::expr::Cond _s0;
  };

  using _Frame =
      std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args) -> void {
                        _result = _args.d_a0;
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args)
                          -> void {
                        _stack.push_back(_Call1{});
                        _stack.push_back(_Enter{_args.d_a0});
                      },
                      [&](const typename LoopifyExpr::expr::Add _args) -> void {
                        _stack.push_back(_Call2{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args) -> void {
                        _stack.push_back(_Call4{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args)
                          -> void {
                        _stack.push_back(_Call6{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      }},
                  e->v());
            },
            [&](_Call1 _f) { _result = (_result + 1); },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call3 _f) { _result = (_result + _f._s0); },
            [&](_Call4 _f) {
              _stack.push_back(_Call5{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call5 _f) { _result = (_result * _f._s0); },
            [&](_Call6 _f) {
              const typename LoopifyExpr::expr::Cond _args = _f._s0;
              unsigned int _cond0 = _result;
              if (0u < _cond0) {
                _stack.push_back(_Enter{_args.d_a1});
              } else {
                _stack.push_back(_Enter{_args.d_a2});
              }
            }},
        _frame);
  }
  return _result;
}

/// depth e computes expression depth.
__attribute__((pure)) unsigned int
LoopifyExpr::depth(const std::shared_ptr<LoopifyExpr::expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::expr> e;
  };

  struct _Call1 {};

  struct _Call2 {
    decltype(std::declval<const typename LoopifyExpr::expr::Add &>().d_a0) _s0;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  struct _Call4 {
    decltype(std::declval<const typename LoopifyExpr::expr::Mul &>().d_a0) _s0;
  };

  struct _Call5 {
    unsigned int _s0;
  };

  struct _Call6 {
    const std::shared_ptr<LoopifyExpr::expr> _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call7 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call8 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5,
                              _Call6, _Call7, _Call8>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args) -> void {
                        _result = 0u;
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args)
                          -> void {
                        _stack.push_back(_Call1{});
                        _stack.push_back(_Enter{_args.d_a0});
                      },
                      [&](const typename LoopifyExpr::expr::Add _args) -> void {
                        _stack.push_back(_Call2{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args) -> void {
                        _stack.push_back(_Call4{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args)
                          -> void {
                        _stack.push_back(_Call6{_args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  e->v());
            },
            [&](_Call1 _f) { _result = (_result + 1); },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call3 _f) { _result = (std::max(_result, _f._s0) + 1); },
            [&](_Call4 _f) {
              _stack.push_back(_Call5{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call5 _f) { _result = (std::max(_result, _f._s0) + 1); },
            [&](_Call6 _f) {
              _stack.push_back(_Call7{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call7 _f) {
              _stack.push_back(_Call8{_f._s0, _result});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call8 _f) {
              _result = (std::max(_result, std::max(_f._s1, _f._s0)) + 1);
            }},
        _frame);
  }
  return _result;
}

/// count_vals e counts the number of Val nodes.
__attribute__((pure)) unsigned int
LoopifyExpr::count_vals(const std::shared_ptr<LoopifyExpr::expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::expr> e;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyExpr::expr::Add &>().d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    decltype(std::declval<const typename LoopifyExpr::expr::Mul &>().d_a0) _s0;
  };

  struct _Call4 {
    unsigned int _s0;
  };

  struct _Call5 {
    const std::shared_ptr<LoopifyExpr::expr> _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call6 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call7 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5,
                              _Call6, _Call7>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args) -> void {
                        _result = 1u;
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args)
                          -> void { _stack.push_back(_Enter{_args.d_a0}); },
                      [&](const typename LoopifyExpr::expr::Add _args) -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args) -> void {
                        _stack.push_back(_Call3{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args)
                          -> void {
                        _stack.push_back(_Call5{_args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call4 _f) { _result = (_result + _f._s0); },
            [&](_Call5 _f) {
              _stack.push_back(_Call6{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call6 _f) {
              _stack.push_back(_Call7{_f._s0, _result});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call7 _f) { _result = (_result + (_f._s1 + _f._s0)); }},
        _frame);
  }
  return _result;
}

/// size e counts total number of nodes.
__attribute__((pure)) unsigned int
LoopifyExpr::size(const std::shared_ptr<LoopifyExpr::expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::expr> e;
  };

  struct _Call1 {};

  struct _Call2 {
    decltype(std::declval<const typename LoopifyExpr::expr::Add &>().d_a0) _s0;
  };

  struct _Call3 {
    unsigned int _s0;
  };

  struct _Call4 {
    decltype(std::declval<const typename LoopifyExpr::expr::Mul &>().d_a0) _s0;
  };

  struct _Call5 {
    unsigned int _s0;
  };

  struct _Call6 {
    const std::shared_ptr<LoopifyExpr::expr> _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call7 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call8 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5,
                              _Call6, _Call7, _Call8>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args) -> void {
                        _result = 1u;
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args)
                          -> void {
                        _stack.push_back(_Call1{});
                        _stack.push_back(_Enter{_args.d_a0});
                      },
                      [&](const typename LoopifyExpr::expr::Add _args) -> void {
                        _stack.push_back(_Call2{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args) -> void {
                        _stack.push_back(_Call4{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args)
                          -> void {
                        _stack.push_back(_Call6{_args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  e->v());
            },
            [&](_Call1 _f) { _result = (_result + 1); },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call3 _f) { _result = ((_result + _f._s0) + 1); },
            [&](_Call4 _f) {
              _stack.push_back(_Call5{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call5 _f) { _result = ((_result + _f._s0) + 1); },
            [&](_Call6 _f) {
              _stack.push_back(_Call7{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call7 _f) {
              _stack.push_back(_Call8{_f._s0, _result});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call8 _f) { _result = ((_result + (_f._s1 + _f._s0)) + 1); }},
        _frame);
  }
  return _result;
}

/// simplify e performs algebraic simplification:
/// Add(x, Val 0) = x, Add(Val 0, x) = x,
/// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
/// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
std::shared_ptr<LoopifyExpr::expr>
LoopifyExpr::simplify(const std::shared_ptr<LoopifyExpr::expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::expr> e;
  };

  struct _Call1 {};

  struct _Call10 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call11 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call12 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call13 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call14 {
    const std::shared_ptr<LoopifyExpr::expr> _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call15 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
    const std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call16 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
    std::shared_ptr<LoopifyExpr::expr> _s1;
  };

  struct _Call2 {
    const typename LoopifyExpr::expr::Add _s0;
  };

  struct _Call3 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call4 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call5 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call6 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call7 {
    std::shared_ptr<LoopifyExpr::expr> _s0;
  };

  struct _Call8 {
    const typename LoopifyExpr::expr::Mul _s0;
  };

  struct _Call9 {
    const typename LoopifyExpr::expr::Val _s0;
  };

  using _Frame =
      std::variant<_Enter, _Call1, _Call10, _Call11, _Call12, _Call13, _Call14,
                   _Call15, _Call16, _Call2, _Call3, _Call4, _Call5, _Call6,
                   _Call7, _Call8, _Call9>;
  std::shared_ptr<LoopifyExpr::expr> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args) -> void {
                        _result = expr::ctor::Val_(_args.d_a0);
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args)
                          -> void {
                        _stack.push_back(_Call1{});
                        _stack.push_back(_Enter{_args.d_a0});
                      },
                      [&](const typename LoopifyExpr::expr::Add _args) -> void {
                        _stack.push_back(_Call2{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args) -> void {
                        _stack.push_back(_Call8{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args)
                          -> void {
                        _stack.push_back(_Call14{_args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  e->v());
            },
            [&](_Call1 _f) { _result = expr::ctor::Succ_(_result); },
            [&](_Call10 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args1)
                          -> void {
                        if (_args1.d_a0 <= 0) {
                          _result = expr::ctor::Val_(0u);
                        } else {
                          unsigned int _x = _args1.d_a0 - 1;
                          if (std::move(_args1.d_a0) == 1u) {
                            _result = s1;
                          } else {
                            _result = expr::ctor::Mul_(
                                s1, expr::ctor::Val_(std::move(_args1.d_a0)));
                          }
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1), expr::ctor::Succ_(_args1.d_a0));
                      },
                      [&](const typename LoopifyExpr::expr::Add _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                              _args1.d_a2));
                      }},
                  _result->v());
            },
            [&](_Call11 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args1)
                          -> void {
                        if (_args1.d_a0 <= 0) {
                          _result = expr::ctor::Val_(0u);
                        } else {
                          unsigned int _x = _args1.d_a0 - 1;
                          if (std::move(_args1.d_a0) == 1u) {
                            _result = s1;
                          } else {
                            _result = expr::ctor::Mul_(
                                s1, expr::ctor::Val_(std::move(_args1.d_a0)));
                          }
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1), expr::ctor::Succ_(_args1.d_a0));
                      },
                      [&](const typename LoopifyExpr::expr::Add _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                              _args1.d_a2));
                      }},
                  _result->v());
            },
            [&](_Call12 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args1)
                          -> void {
                        if (_args1.d_a0 <= 0) {
                          _result = expr::ctor::Val_(0u);
                        } else {
                          unsigned int _x = _args1.d_a0 - 1;
                          if (std::move(_args1.d_a0) == 1u) {
                            _result = s1;
                          } else {
                            _result = expr::ctor::Mul_(
                                s1, expr::ctor::Val_(std::move(_args1.d_a0)));
                          }
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1), expr::ctor::Succ_(_args1.d_a0));
                      },
                      [&](const typename LoopifyExpr::expr::Add _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                              _args1.d_a2));
                      }},
                  _result->v());
            },
            [&](_Call13 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args1)
                          -> void {
                        if (_args1.d_a0 <= 0) {
                          _result = expr::ctor::Val_(0u);
                        } else {
                          unsigned int _x = _args1.d_a0 - 1;
                          if (std::move(_args1.d_a0) == 1u) {
                            _result = s1;
                          } else {
                            _result = expr::ctor::Mul_(
                                s1, expr::ctor::Val_(std::move(_args1.d_a0)));
                          }
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1), expr::ctor::Succ_(_args1.d_a0));
                      },
                      [&](const typename LoopifyExpr::expr::Add _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args1)
                          -> void {
                        _result = expr::ctor::Mul_(
                            std::move(s1),
                            expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                              _args1.d_a2));
                      }},
                  _result->v());
            },
            [&](_Call14 _f) {
              _stack.push_back(_Call15{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call15 _f) {
              _stack.push_back(_Call16{_f._s0, _result});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call16 _f) {
              _result = expr::ctor::Cond_(_result, _f._s1, _f._s0);
            },
            [&](_Call2 _f) {
              const typename LoopifyExpr::expr::Add _args = _f._s0;
              std::visit(
                  Overloaded{[&](const typename LoopifyExpr::expr::Val _args0)
                                 -> void {
                               if (_args0.d_a0 <= 0) {
                                 _stack.push_back(_Enter{_args.d_a1});
                               } else {
                                 unsigned int n0 = _args0.d_a0 - 1;
                                 std::shared_ptr<LoopifyExpr::expr> s1 =
                                     expr::ctor::Val_((n0 + 1));
                                 _stack.push_back(_Call3{s1});
                                 _stack.push_back(_Enter{_args.d_a1});
                               }
                             },
                             [&](const typename LoopifyExpr::expr::Succ _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Succ_(_args0.d_a0);
                               _stack.push_back(_Call4{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             },
                             [&](const typename LoopifyExpr::expr::Add _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Add_(_args0.d_a0, _args0.d_a1);
                               _stack.push_back(_Call5{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             },
                             [&](const typename LoopifyExpr::expr::Mul _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Mul_(_args0.d_a0, _args0.d_a1);
                               _stack.push_back(_Call6{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             },
                             [&](const typename LoopifyExpr::expr::Cond _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Cond_(_args0.d_a0, _args0.d_a1,
                                                     _args0.d_a2);
                               _stack.push_back(_Call7{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                  _result->v());
            },
            [&](_Call3 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{[&](const typename LoopifyExpr::expr::Val _args1)
                                 -> void {
                               if (_args1.d_a0 <= 0) {
                                 _result = std::move(s1);
                               } else {
                                 unsigned int n2 = _args1.d_a0 - 1;
                                 _result = expr::ctor::Add_(
                                     s1, expr::ctor::Val_((n2 + 1)));
                               }
                             },
                             [&](const typename LoopifyExpr::expr::Succ _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Succ_(_args1.d_a0));
                             },
                             [&](const typename LoopifyExpr::expr::Add _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Mul _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Cond _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                             }},
                  _result->v());
            },
            [&](_Call4 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{[&](const typename LoopifyExpr::expr::Val _args1)
                                 -> void {
                               if (_args1.d_a0 <= 0) {
                                 _result = std::move(s1);
                               } else {
                                 unsigned int n0 = _args1.d_a0 - 1;
                                 _result = expr::ctor::Add_(
                                     s1, expr::ctor::Val_((n0 + 1)));
                               }
                             },
                             [&](const typename LoopifyExpr::expr::Succ _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Succ_(_args1.d_a0));
                             },
                             [&](const typename LoopifyExpr::expr::Add _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Mul _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Cond _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                             }},
                  _result->v());
            },
            [&](_Call5 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{[&](const typename LoopifyExpr::expr::Val _args1)
                                 -> void {
                               if (_args1.d_a0 <= 0) {
                                 _result = std::move(s1);
                               } else {
                                 unsigned int n0 = _args1.d_a0 - 1;
                                 _result = expr::ctor::Add_(
                                     s1, expr::ctor::Val_((n0 + 1)));
                               }
                             },
                             [&](const typename LoopifyExpr::expr::Succ _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Succ_(_args1.d_a0));
                             },
                             [&](const typename LoopifyExpr::expr::Add _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Mul _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Cond _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                             }},
                  _result->v());
            },
            [&](_Call6 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{[&](const typename LoopifyExpr::expr::Val _args1)
                                 -> void {
                               if (_args1.d_a0 <= 0) {
                                 _result = std::move(s1);
                               } else {
                                 unsigned int n0 = _args1.d_a0 - 1;
                                 _result = expr::ctor::Add_(
                                     s1, expr::ctor::Val_((n0 + 1)));
                               }
                             },
                             [&](const typename LoopifyExpr::expr::Succ _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Succ_(_args1.d_a0));
                             },
                             [&](const typename LoopifyExpr::expr::Add _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Mul _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Cond _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                             }},
                  _result->v());
            },
            [&](_Call7 _f) {
              std::shared_ptr<LoopifyExpr::expr> s1 = _f._s0;
              std::visit(
                  Overloaded{[&](const typename LoopifyExpr::expr::Val _args1)
                                 -> void {
                               if (_args1.d_a0 <= 0) {
                                 _result = std::move(s1);
                               } else {
                                 unsigned int n0 = _args1.d_a0 - 1;
                                 _result = expr::ctor::Add_(
                                     s1, expr::ctor::Val_((n0 + 1)));
                               }
                             },
                             [&](const typename LoopifyExpr::expr::Succ _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Succ_(_args1.d_a0));
                             },
                             [&](const typename LoopifyExpr::expr::Add _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Add_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Mul _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Mul_(_args1.d_a0, _args1.d_a1));
                             },
                             [&](const typename LoopifyExpr::expr::Cond _args1)
                                 -> void {
                               _result = expr::ctor::Add_(
                                   std::move(s1),
                                   expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                             }},
                  _result->v());
            },
            [&](_Call8 _f) {
              const typename LoopifyExpr::expr::Mul _args = _f._s0;
              std::visit(
                  Overloaded{[&](const typename LoopifyExpr::expr::Val _args0)
                                 -> void {
                               if (_args0.d_a0 <= 0) {
                                 _result = expr::ctor::Val_(0u);
                               } else {
                                 unsigned int _x = _args0.d_a0 - 1;
                                 _stack.push_back(_Call9{_args0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               }
                             },
                             [&](const typename LoopifyExpr::expr::Succ _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Succ_(_args0.d_a0);
                               _stack.push_back(_Call10{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             },
                             [&](const typename LoopifyExpr::expr::Add _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Add_(_args0.d_a0, _args0.d_a1);
                               _stack.push_back(_Call11{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             },
                             [&](const typename LoopifyExpr::expr::Mul _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Mul_(_args0.d_a0, _args0.d_a1);
                               _stack.push_back(_Call12{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             },
                             [&](const typename LoopifyExpr::expr::Cond _args0)
                                 -> void {
                               std::shared_ptr<LoopifyExpr::expr> s1 =
                                   expr::ctor::Cond_(_args0.d_a0, _args0.d_a1,
                                                     _args0.d_a2);
                               _stack.push_back(_Call13{s1});
                               _stack.push_back(_Enter{_args.d_a1});
                             }},
                  _result->v());
            },
            [&](_Call9 _f) {
              const typename LoopifyExpr::expr::Val _args0 = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::expr::Val _args1)
                          -> void {
                        if (_args1.d_a0 <= 0) {
                          _result = expr::ctor::Val_(0u);
                        } else {
                          unsigned int n1 = _args1.d_a0 - 1;
                          std::shared_ptr<LoopifyExpr::expr> s2 =
                              expr::ctor::Val_((n1 + 1));
                          if (_args0.d_a0 == 1u) {
                            _result = std::move(s2);
                          } else {
                            _result = expr::ctor::Mul_(
                                expr::ctor::Val_(_args0.d_a0), std::move(s2));
                          }
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Succ _args1)
                          -> void {
                        std::shared_ptr<LoopifyExpr::expr> s2 =
                            expr::ctor::Succ_(_args1.d_a0);
                        if (_args0.d_a0 == 1u) {
                          _result = std::move(s2);
                        } else {
                          _result = expr::ctor::Mul_(
                              expr::ctor::Val_(_args0.d_a0), std::move(s2));
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Add _args1)
                          -> void {
                        std::shared_ptr<LoopifyExpr::expr> s2 =
                            expr::ctor::Add_(_args1.d_a0, _args1.d_a1);
                        if (_args0.d_a0 == 1u) {
                          _result = std::move(s2);
                        } else {
                          _result = expr::ctor::Mul_(
                              expr::ctor::Val_(_args0.d_a0), std::move(s2));
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Mul _args1)
                          -> void {
                        std::shared_ptr<LoopifyExpr::expr> s2 =
                            expr::ctor::Mul_(_args1.d_a0, _args1.d_a1);
                        if (_args0.d_a0 == 1u) {
                          _result = std::move(s2);
                        } else {
                          _result = expr::ctor::Mul_(
                              expr::ctor::Val_(_args0.d_a0), std::move(s2));
                        }
                      },
                      [&](const typename LoopifyExpr::expr::Cond _args1)
                          -> void {
                        std::shared_ptr<LoopifyExpr::expr> s2 =
                            expr::ctor::Cond_(_args1.d_a0, _args1.d_a1,
                                              _args1.d_a2);
                        if (_args0.d_a0 == 1u) {
                          _result = std::move(s2);
                        } else {
                          _result = expr::ctor::Mul_(
                              expr::ctor::Val_(_args0.d_a0), std::move(s2));
                        }
                      }},
                  _result->v());
            }},
        _frame);
  }
  return _result;
}

/// eval_simple e evaluates simple expression with positive test.
__attribute__((pure)) unsigned int
LoopifyExpr::eval_simple(const std::shared_ptr<LoopifyExpr::simple_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::simple_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyExpr::simple_expr::Plus &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    const typename LoopifyExpr::simple_expr::IfPos _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::simple_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::simple_expr::Lit _args)
                          -> void { _result = _args.d_a0; },
                      [&](const typename LoopifyExpr::simple_expr::Plus _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::simple_expr::IfPos _args)
                          -> void {
                        _stack.push_back(_Call3{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); },
            [&](_Call3 _f) {
              const typename LoopifyExpr::simple_expr::IfPos _args = _f._s0;
              unsigned int _cond0 = _result;
              if (0u < _cond0) {
                _stack.push_back(_Enter{_args.d_a1});
              } else {
                _stack.push_back(_Enter{_args.d_a2});
              }
            }},
        _frame);
  }
  return _result;
}

/// depth_simple e computes depth of simple expression tree.
__attribute__((pure)) unsigned int
LoopifyExpr::depth_simple(const std::shared_ptr<LoopifyExpr::simple_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::simple_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyExpr::simple_expr::Plus &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    const std::shared_ptr<LoopifyExpr::simple_expr> _s0;
    const std::shared_ptr<LoopifyExpr::simple_expr> _s1;
  };

  struct _Call4 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyExpr::simple_expr> _s1;
  };

  struct _Call5 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::simple_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::simple_expr::Lit _args)
                          -> void { _result = 0u; },
                      [&](const typename LoopifyExpr::simple_expr::Plus _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::simple_expr::IfPos _args)
                          -> void {
                        _stack.push_back(_Call3{_args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (std::max(_result, _f._s0) + 1); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call4 _f) {
              _stack.push_back(_Call5{_f._s0, _result});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call5 _f) {
              _result = (std::max(_result, std::max(_f._s1, _f._s0)) + 1);
            }},
        _frame);
  }
  return _result;
}

/// sum_shapes l sums values from shapes using unified pattern.
/// Tests or-pattern style matching in Coq.
__attribute__((pure)) unsigned int LoopifyExpr::sum_shapes(
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l;
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
              const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Nil _args)
                          -> void { _result = 0u; },
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Cons _args)
                          -> void {
                        unsigned int val = std::visit(
                            Overloaded{
                                [](const typename LoopifyExpr::shape::Circle
                                       _args0) -> unsigned int {
                                  return _args0.d_a0;
                                },
                                [](const typename LoopifyExpr::shape::Square
                                       _args0) -> unsigned int {
                                  return _args0.d_a0;
                                },
                                [](const typename LoopifyExpr::shape::Triangle
                                       _args0) -> unsigned int {
                                  return _args0.d_a0;
                                }},
                            _args.d_a0->v());
                        _stack.push_back(_Call1{std::move(val)});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); }},
        _frame);
  }
  return _result;
}

/// count_by_shape l counts shapes: (circles, squares, triangles).
__attribute__((pure))
std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
LoopifyExpr::count_by_shape(
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> &l) {
  struct _Enter {
    const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>> l;
  };

  struct _Call1 {
    const typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons _s0;
  };

  using _Frame = std::variant<_Enter, _Call1>;
  std::pair<std::pair<unsigned int, unsigned int>, unsigned int> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{l});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<List<std::shared_ptr<LoopifyExpr::shape>>>
                  l = _f.l;
              std::visit(
                  Overloaded{
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Nil _args)
                          -> void {
                        _result = std::make_pair(std::make_pair(0u, 0u), 0u);
                      },
                      [&](const typename List<
                          std::shared_ptr<LoopifyExpr::shape>>::Cons _args)
                          -> void {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  l->v());
            },
            [&](_Call1 _f) {
              const typename List<std::shared_ptr<LoopifyExpr::shape>>::Cons
                  _args = _f._s0;
              std::pair<unsigned int, unsigned int> p = _result.first;
              unsigned int t = _result.second;
              unsigned int c = p.first;
              unsigned int sq = p.second;
              _result = std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::shape::Circle _args0)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(std::make_pair((c + 1), sq), t);
                      },
                      [&](const typename LoopifyExpr::shape::Square _args0)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(std::make_pair(c, (sq + 1)), t);
                      },
                      [&](const typename LoopifyExpr::shape::Triangle _args0)
                          -> std::pair<std::pair<unsigned int, unsigned int>,
                                       unsigned int> {
                        return std::make_pair(std::make_pair(c, sq), (t + 1));
                      }},
                  _args.d_a0->v());
            }},
        _frame);
  }
  return _result;
}

/// eval_cond e evaluates conditional expression.
__attribute__((pure)) unsigned int
LoopifyExpr::eval_cond(const std::shared_ptr<LoopifyExpr::cond_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::cond_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyExpr::cond_expr::CPlus &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    const typename LoopifyExpr::cond_expr::CCond _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::cond_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::cond_expr::CLit _args)
                          -> void { _result = _args.d_a0; },
                      [&](const typename LoopifyExpr::cond_expr::CPlus _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::cond_expr::CCond _args)
                          -> void {
                        _stack.push_back(_Call3{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); },
            [&](_Call3 _f) {
              const typename LoopifyExpr::cond_expr::CCond _args = _f._s0;
              unsigned int _cond0 = _result;
              if (0u < _cond0) {
                _stack.push_back(_Enter{_args.d_a1});
              } else {
                _stack.push_back(_Enter{_args.d_a2});
              }
            }},
        _frame);
  }
  return _result;
}

/// depth_cond e computes depth of conditional expression tree.
__attribute__((pure)) unsigned int
LoopifyExpr::depth_cond(const std::shared_ptr<LoopifyExpr::cond_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExpr::cond_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<const typename LoopifyExpr::cond_expr::CPlus &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    const std::shared_ptr<LoopifyExpr::cond_expr> _s0;
    const std::shared_ptr<LoopifyExpr::cond_expr> _s1;
  };

  struct _Call4 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyExpr::cond_expr> _s1;
  };

  struct _Call5 {
    unsigned int _s0;
    unsigned int _s1;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
  unsigned int _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExpr::cond_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExpr::cond_expr::CLit _args)
                          -> void { _result = 0u; },
                      [&](const typename LoopifyExpr::cond_expr::CPlus _args)
                          -> void {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExpr::cond_expr::CCond _args)
                          -> void {
                        _stack.push_back(_Call3{_args.d_a1, _args.d_a0});
                        _stack.push_back(_Enter{_args.d_a2});
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (std::max(_result, _f._s0) + 1); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call4 _f) {
              _stack.push_back(_Call5{_f._s0, _result});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call5 _f) {
              _result = (std::max(_result, std::max(_f._s1, _f._s0)) + 1);
            }},
        _frame);
  }
  return _result;
}
