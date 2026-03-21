#include <loopify_expr_variants.h>

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

__attribute__((pure)) unsigned int LoopifyExprVariants::eval_cond(
    const std::shared_ptr<LoopifyExprVariants::cond_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::cond_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::cond_expr::Add &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    const typename LoopifyExprVariants::cond_expr::Cond _s0;
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
              const std::shared_ptr<LoopifyExprVariants::cond_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::cond_expr::Lit
                              _args) -> unsigned int {
                        _result = _args.d_a0;
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::cond_expr::Add
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::cond_expr::Cond
                              _args) -> unsigned int {
                        _stack.push_back(_Call3{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                        return {};
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_result + _f._s0); },
            [&](_Call3 _f) {
              const typename LoopifyExprVariants::cond_expr::Cond _args =
                  _f._s0;
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

__attribute__((pure)) unsigned int LoopifyExprVariants::size_cond(
    const std::shared_ptr<LoopifyExprVariants::cond_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::cond_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::cond_expr::Add &>()
                 .d_a0) _s0;
    decltype(1u) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(1u) _s1;
  };

  struct _Call3 {
    const std::shared_ptr<LoopifyExprVariants::cond_expr> _s0;
    const std::shared_ptr<LoopifyExprVariants::cond_expr> _s1;
    decltype(1u) _s2;
  };

  struct _Call4 {
    unsigned int _s0;
    const std::shared_ptr<LoopifyExprVariants::cond_expr> _s1;
    decltype(1u) _s2;
  };

  struct _Call5 {
    unsigned int _s0;
    unsigned int _s1;
    decltype(1u) _s2;
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
              const std::shared_ptr<LoopifyExprVariants::cond_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::cond_expr::Lit
                              _args) -> unsigned int {
                        _result = 1u;
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::cond_expr::Add
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::cond_expr::Cond
                              _args) -> unsigned int {
                        _stack.push_back(_Call3{_args.d_a1, _args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a2});
                        return {};
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = ((_f._s1 + _result) + _f._s0); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result, _f._s1, _f._s2});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call4 _f) {
              _stack.push_back(_Call5{_f._s0, _result, _f._s2});
              _stack.push_back(_Enter{_f._s1});
            },
            [&](_Call5 _f) {
              _result = (((_f._s2 + _result) + _f._s1) + _f._s0);
            }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyExprVariants::eval_arith(
    const std::shared_ptr<LoopifyExprVariants::arith_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::arith_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::arith_expr::AAdd &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    unsigned int _s0;
  };

  struct _Call3 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::arith_expr::AMul &>()
                 .d_a0) _s0;
  };

  struct _Call4 {
    unsigned int _s0;
  };

  struct _Call5 {
    const typename LoopifyExprVariants::arith_expr::ADiv _s0;
  };

  struct _Call6 {
    decltype((std::declval<unsigned int &>() + 1)) _s0;
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
              const std::shared_ptr<LoopifyExprVariants::arith_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::arith_expr::ANum
                              _args) -> unsigned int {
                        _result = _args.d_a0;
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::arith_expr::AAdd
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::arith_expr::AMul
                              _args) -> unsigned int {
                        _stack.push_back(_Call3{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::arith_expr::ADiv
                              _args) -> unsigned int {
                        _stack.push_back(_Call5{_args});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
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
            [&](_Call4 _f) { _result = (_result * _f._s0); },
            [&](_Call5 _f) {
              const typename LoopifyExprVariants::arith_expr::ADiv _args =
                  _f._s0;
              if (_result <= 0) {
                _result = 0u;
              } else {
                unsigned int n = _result - 1;
                _stack.push_back(_Call6{(n + 1)});
                _stack.push_back(_Enter{_args.d_a0});
              }
            },
            [&](_Call6 _f) { _result = Nat::div(_result, _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyExprVariants::count_ops(
    const std::shared_ptr<LoopifyExprVariants::arith_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::arith_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::arith_expr::AAdd &>()
                 .d_a0) _s0;
    decltype(1u) _s1;
  };

  struct _Call2 {
    unsigned int _s0;
    decltype(1u) _s1;
  };

  struct _Call3 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::arith_expr::AMul &>()
                 .d_a0) _s0;
    decltype(1u) _s1;
  };

  struct _Call4 {
    unsigned int _s0;
    decltype(1u) _s1;
  };

  struct _Call5 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::arith_expr::ADiv &>()
                 .d_a0) _s0;
    decltype(1u) _s1;
  };

  struct _Call6 {
    unsigned int _s0;
    decltype(1u) _s1;
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
              const std::shared_ptr<LoopifyExprVariants::arith_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::arith_expr::ANum
                              _args) -> unsigned int {
                        _result = 0u;
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::arith_expr::AAdd
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{_args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::arith_expr::AMul
                              _args) -> unsigned int {
                        _stack.push_back(_Call3{_args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::arith_expr::ADiv
                              _args) -> unsigned int {
                        _stack.push_back(_Call5{_args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = ((_f._s1 + _result) + _f._s0); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call4 _f) { _result = ((_f._s1 + _result) + _f._s0); },
            [&](_Call5 _f) {
              _stack.push_back(_Call6{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call6 _f) { _result = ((_f._s1 + _result) + _f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) bool LoopifyExprVariants::eval_bool(
    const std::shared_ptr<LoopifyExprVariants::bool_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::bool_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::bool_expr::BAnd &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    bool _s0;
  };

  struct _Call3 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::bool_expr::BOr &>()
                 .d_a0) _s0;
  };

  struct _Call4 {
    bool _s0;
  };

  struct _Call5 {};

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
  bool _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExprVariants::bool_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args) -> bool {
                        _result = true;
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args) -> bool {
                        _result = false;
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args) -> bool {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args) -> bool {
                        _stack.push_back(_Call3{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args) -> bool {
                        _stack.push_back(_Call5{});
                        _stack.push_back(_Enter{_args.d_a0});
                        return {};
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _stack.push_back(_Call2{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call2 _f) { _result = (_result && _f._s0); },
            [&](_Call3 _f) {
              _stack.push_back(_Call4{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call4 _f) { _result = (_result || _f._s0); },
            [&](_Call5 _f) { _result = !(_result); }},
        _frame);
  }
  return _result;
}

std::shared_ptr<LoopifyExprVariants::bool_expr>
LoopifyExprVariants::simplify_bool(
    const std::shared_ptr<LoopifyExprVariants::bool_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::bool_expr> e;
  };

  struct _Call1 {
    const typename LoopifyExprVariants::bool_expr::BAnd _s0;
  };

  struct _Call10 {
    std::shared_ptr<LoopifyExprVariants::bool_expr> _s0;
  };

  struct _Call11 {};

  struct _Call2 {};

  struct _Call3 {
    std::shared_ptr<LoopifyExprVariants::bool_expr> _s0;
  };

  struct _Call4 {
    std::shared_ptr<LoopifyExprVariants::bool_expr> _s0;
  };

  struct _Call5 {
    std::shared_ptr<LoopifyExprVariants::bool_expr> _s0;
  };

  struct _Call6 {
    const typename LoopifyExprVariants::bool_expr::BOr _s0;
  };

  struct _Call7 {};

  struct _Call8 {
    std::shared_ptr<LoopifyExprVariants::bool_expr> _s0;
  };

  struct _Call9 {
    std::shared_ptr<LoopifyExprVariants::bool_expr> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call10, _Call11, _Call2, _Call3,
                              _Call4, _Call5, _Call6, _Call7, _Call8, _Call9>;
  std::shared_ptr<LoopifyExprVariants::bool_expr> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExprVariants::bool_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args)
                          -> std::shared_ptr<LoopifyExprVariants::bool_expr> {
                        _result = bool_expr::ctor::BTrue_();
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args)
                          -> std::shared_ptr<LoopifyExprVariants::bool_expr> {
                        _result = bool_expr::ctor::BFalse_();
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args)
                          -> std::shared_ptr<LoopifyExprVariants::bool_expr> {
                        _stack.push_back(_Call1{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args)
                          -> std::shared_ptr<LoopifyExprVariants::bool_expr> {
                        _stack.push_back(_Call6{_args});
                        _stack.push_back(_Enter{_args.d_a0});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args)
                          -> std::shared_ptr<LoopifyExprVariants::bool_expr> {
                        _stack.push_back(_Call11{});
                        _stack.push_back(_Enter{_args.d_a0});
                        return {};
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              const typename LoopifyExprVariants::bool_expr::BAnd _args =
                  _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args0) -> void {
                        _stack.push_back(_Call2{});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args0) -> void {
                        _result = bool_expr::ctor::BFalse_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args0) -> void {
                        std::shared_ptr<LoopifyExprVariants::bool_expr> a_ =
                            bool_expr::ctor::BAnd_(_args0.d_a0, _args0.d_a1);
                        _stack.push_back(_Call3{a_});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args0) -> void {
                        std::shared_ptr<LoopifyExprVariants::bool_expr> a_ =
                            bool_expr::ctor::BOr_(_args0.d_a0, _args0.d_a1);
                        _stack.push_back(_Call4{a_});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args0) -> void {
                        std::shared_ptr<LoopifyExprVariants::bool_expr> a_ =
                            bool_expr::ctor::BNot_(_args0.d_a0);
                        _stack.push_back(_Call5{a_});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  _result->v());
            },
            [&](_Call10 _f) {
              std::shared_ptr<LoopifyExprVariants::bool_expr> a_ = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void {
                        _result = bool_expr::ctor::BTrue_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void { _result = std::move(a_); },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_),
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_),
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_), bool_expr::ctor::BNot_(_args1.d_a0));
                      }},
                  _result->v());
            },
            [&](_Call11 _f) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args0) -> void {
                        _result = bool_expr::ctor::BFalse_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args0) -> void {
                        _result = bool_expr::ctor::BTrue_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args0) -> void {
                        _result = bool_expr::ctor::BNot_(
                            bool_expr::ctor::BAnd_(_args0.d_a0, _args0.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args0) -> void {
                        _result = bool_expr::ctor::BNot_(
                            bool_expr::ctor::BOr_(_args0.d_a0, _args0.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args0) -> void {
                        _result = bool_expr::ctor::BNot_(
                            bool_expr::ctor::BNot_(_args0.d_a0));
                      }},
                  _result->v());
            },
            [&](_Call2 _f) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void {
                        _result = bool_expr::ctor::BTrue_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void {
                        _result = bool_expr::ctor::BFalse_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result =
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1);
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result =
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1);
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BNot_(_args1.d_a0);
                      }},
                  _result->v());
            },
            [&](_Call3 _f) {
              std::shared_ptr<LoopifyExprVariants::bool_expr> a_ = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void { _result = std::move(a_); },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void {
                        _result = bool_expr::ctor::BFalse_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_),
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_),
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_), bool_expr::ctor::BNot_(_args1.d_a0));
                      }},
                  _result->v());
            },
            [&](_Call4 _f) {
              std::shared_ptr<LoopifyExprVariants::bool_expr> a_ = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void { _result = std::move(a_); },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void {
                        _result = bool_expr::ctor::BFalse_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_),
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_),
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_), bool_expr::ctor::BNot_(_args1.d_a0));
                      }},
                  _result->v());
            },
            [&](_Call5 _f) {
              std::shared_ptr<LoopifyExprVariants::bool_expr> a_ = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void { _result = std::move(a_); },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void {
                        _result = bool_expr::ctor::BFalse_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_),
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_),
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BAnd_(
                            std::move(a_), bool_expr::ctor::BNot_(_args1.d_a0));
                      }},
                  _result->v());
            },
            [&](_Call6 _f) {
              const typename LoopifyExprVariants::bool_expr::BOr _args = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args0) -> void {
                        _result = bool_expr::ctor::BTrue_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args0) -> void {
                        _stack.push_back(_Call7{});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args0) -> void {
                        std::shared_ptr<LoopifyExprVariants::bool_expr> a_ =
                            bool_expr::ctor::BAnd_(_args0.d_a0, _args0.d_a1);
                        _stack.push_back(_Call8{a_});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args0) -> void {
                        std::shared_ptr<LoopifyExprVariants::bool_expr> a_ =
                            bool_expr::ctor::BOr_(_args0.d_a0, _args0.d_a1);
                        _stack.push_back(_Call9{a_});
                        _stack.push_back(_Enter{_args.d_a1});
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args0) -> void {
                        std::shared_ptr<LoopifyExprVariants::bool_expr> a_ =
                            bool_expr::ctor::BNot_(_args0.d_a0);
                        _stack.push_back(_Call10{a_});
                        _stack.push_back(_Enter{_args.d_a1});
                      }},
                  _result->v());
            },
            [&](_Call7 _f) {
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void {
                        _result = bool_expr::ctor::BTrue_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void {
                        _result = bool_expr::ctor::BFalse_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result =
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1);
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result =
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1);
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BNot_(_args1.d_a0);
                      }},
                  _result->v());
            },
            [&](_Call8 _f) {
              std::shared_ptr<LoopifyExprVariants::bool_expr> a_ = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void {
                        _result = bool_expr::ctor::BTrue_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void { _result = std::move(a_); },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_),
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_),
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_), bool_expr::ctor::BNot_(_args1.d_a0));
                      }},
                  _result->v());
            },
            [&](_Call9 _f) {
              std::shared_ptr<LoopifyExprVariants::bool_expr> a_ = _f._s0;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::bool_expr::BTrue
                              _args1) -> void {
                        _result = bool_expr::ctor::BTrue_();
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BFalse
                              _args1) -> void { _result = std::move(a_); },
                      [&](const typename LoopifyExprVariants::bool_expr::BAnd
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_),
                            bool_expr::ctor::BAnd_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BOr
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_),
                            bool_expr::ctor::BOr_(_args1.d_a0, _args1.d_a1));
                      },
                      [&](const typename LoopifyExprVariants::bool_expr::BNot
                              _args1) -> void {
                        _result = bool_expr::ctor::BOr_(
                            std::move(a_), bool_expr::ctor::BNot_(_args1.d_a0));
                      }},
                  _result->v());
            }},
        _frame);
  }
  return _result;
}

std::shared_ptr<List<unsigned int>> LoopifyExprVariants::eval_list(
    const std::shared_ptr<LoopifyExprVariants::list_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::list_expr> e;
  };

  struct _Call1 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::list_expr::LCons &>()
                 .d_a0) _s0;
  };

  struct _Call2 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::list_expr::LAppend &>()
                 .d_a0) _s0;
  };

  struct _Call3 {
    std::shared_ptr<List<unsigned int>> _s0;
  };

  using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
  std::shared_ptr<List<unsigned int>> _result{};
  std::vector<_Frame> _stack;
  _stack.push_back(_Enter{e});
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    std::visit(
        Overloaded{
            [&](_Enter _f) {
              const std::shared_ptr<LoopifyExprVariants::list_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::list_expr::LNil
                              _args) -> std::shared_ptr<List<unsigned int>> {
                        _result = List<unsigned int>::ctor::Nil_();
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::list_expr::LCons
                              _args) -> std::shared_ptr<List<unsigned int>> {
                        _stack.push_back(_Call1{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::list_expr::LAppend
                              _args) -> std::shared_ptr<List<unsigned int>> {
                        _stack.push_back(_Call2{_args.d_a0});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::list_expr::
                              LReplicate _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        _result = ListDef::template repeat<unsigned int>(
                            _args.d_a1, _args.d_a0);
                        return {};
                      }},
                  e->v());
            },
            [&](_Call1 _f) {
              _result = List<unsigned int>::ctor::Cons_(_f._s0, _result);
            },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call3 _f) { _result = _result->app(_f._s0); }},
        _frame);
  }
  return _result;
}

__attribute__((pure)) unsigned int LoopifyExprVariants::list_expr_size(
    const std::shared_ptr<LoopifyExprVariants::list_expr> &e) {
  struct _Enter {
    const std::shared_ptr<LoopifyExprVariants::list_expr> e;
  };

  struct _Call1 {
    decltype(1u) _s0;
  };

  struct _Call2 {
    decltype(std::declval<
                 const typename LoopifyExprVariants::list_expr::LAppend &>()
                 .d_a0) _s0;
    decltype(1u) _s1;
  };

  struct _Call3 {
    unsigned int _s0;
    decltype(1u) _s1;
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
              const std::shared_ptr<LoopifyExprVariants::list_expr> e = _f.e;
              std::visit(
                  Overloaded{
                      [&](const typename LoopifyExprVariants::list_expr::LNil
                              _args) -> unsigned int {
                        _result = 1u;
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::list_expr::LCons
                              _args) -> unsigned int {
                        _stack.push_back(_Call1{1u});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::list_expr::LAppend
                              _args) -> unsigned int {
                        _stack.push_back(_Call2{_args.d_a0, 1u});
                        _stack.push_back(_Enter{_args.d_a1});
                        return {};
                      },
                      [&](const typename LoopifyExprVariants::list_expr::
                              LReplicate _args) -> unsigned int {
                        _result = 1u;
                        return {};
                      }},
                  e->v());
            },
            [&](_Call1 _f) { _result = (_f._s0 + _result); },
            [&](_Call2 _f) {
              _stack.push_back(_Call3{_result, _f._s1});
              _stack.push_back(_Enter{_f._s0});
            },
            [&](_Call3 _f) { _result = ((_f._s1 + _result) + _f._s0); }},
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
