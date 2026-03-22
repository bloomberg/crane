#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct LoopifyExpr {
  /// Simple expression ADT with multiple recursive constructors.
  struct expr {
    // TYPES
    struct Val {
      unsigned int d_a0;
    };

    struct Succ {
      std::shared_ptr<expr> d_a0;
    };

    struct Add {
      std::shared_ptr<expr> d_a0;
      std::shared_ptr<expr> d_a1;
    };

    struct Mul {
      std::shared_ptr<expr> d_a0;
      std::shared_ptr<expr> d_a1;
    };

    struct Cond {
      std::shared_ptr<expr> d_a0;
      std::shared_ptr<expr> d_a1;
      std::shared_ptr<expr> d_a2;
    };

    using variant_t = std::variant<Val, Succ, Add, Mul, Cond>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit expr(Val _v) : d_v_(std::move(_v)) {}

    explicit expr(Succ _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    explicit expr(Cond _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<expr> Val_(unsigned int a0) {
        return std::shared_ptr<expr>(new expr(Val{a0}));
      }

      static std::shared_ptr<expr> Succ_(const std::shared_ptr<expr> &a0) {
        return std::shared_ptr<expr>(new expr(Succ{a0}));
      }

      static std::shared_ptr<expr> Add_(const std::shared_ptr<expr> &a0,
                                        const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<expr>(new expr(Add{a0, a1}));
      }

      static std::shared_ptr<expr> Mul_(const std::shared_ptr<expr> &a0,
                                        const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<expr>(new expr(Mul{a0, a1}));
      }

      static std::shared_ptr<expr> Cond_(const std::shared_ptr<expr> &a0,
                                         const std::shared_ptr<expr> &a1,
                                         const std::shared_ptr<expr> &a2) {
        return std::shared_ptr<expr>(new expr(Cond{a0, a1, a2}));
      }

      static std::unique_ptr<expr> Val_uptr(unsigned int a0) {
        return std::unique_ptr<expr>(new expr(Val{a0}));
      }

      static std::unique_ptr<expr> Succ_uptr(const std::shared_ptr<expr> &a0) {
        return std::unique_ptr<expr>(new expr(Succ{a0}));
      }

      static std::unique_ptr<expr> Add_uptr(const std::shared_ptr<expr> &a0,
                                            const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<expr>(new expr(Add{a0, a1}));
      }

      static std::unique_ptr<expr> Mul_uptr(const std::shared_ptr<expr> &a0,
                                            const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<expr>(new expr(Mul{a0, a1}));
      }

      static std::unique_ptr<expr> Cond_uptr(const std::shared_ptr<expr> &a0,
                                             const std::shared_ptr<expr> &a1,
                                             const std::shared_ptr<expr> &a2) {
        return std::unique_ptr<expr>(new expr(Cond{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<expr>, T1> F1,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F3,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1,
                   std::shared_ptr<expr>, T1>
                F4>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const std::shared_ptr<expr> &e) {
    struct _Enter {
      const std::shared_ptr<expr> e;
    };

    struct _Call1 {
      decltype(std::declval<const typename expr::Succ &>().d_a0) _s0;
    };

    struct _Call2 {
      decltype(std::declval<const typename expr::Add &>().d_a0) _s0;
      decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
    };

    struct _Call3 {
      T1 _s0;
      decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
    };

    struct _Call4 {
      decltype(std::declval<const typename expr::Mul &>().d_a0) _s0;
      decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
    };

    struct _Call5 {
      T1 _s0;
      decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
    };

    struct _Call6 {
      const std::shared_ptr<expr> _s0;
      const std::shared_ptr<expr> _s1;
      decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
    };

    struct _Call7 {
      T1 _s0;
      const std::shared_ptr<expr> _s1;
      decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
    };

    struct _Call8 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5,
                                _Call6, _Call7, _Call8>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{e});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<expr> e = _f.e;
                std::visit(
                    Overloaded{[&](const typename expr::Val _args) -> void {
                                 _result = f(_args.d_a0);
                               },
                               [&](const typename expr::Succ _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a0});
                               },
                               [&](const typename expr::Add _args) -> void {
                                 _stack.push_back(_Call2{_args.d_a0, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               },
                               [&](const typename expr::Mul _args) -> void {
                                 _stack.push_back(_Call4{_args.d_a0, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               },
                               [&](const typename expr::Cond _args) -> void {
                                 _stack.push_back(_Call6{_args.d_a1, _args.d_a0,
                                                         _args.d_a2, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    e->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s0, _result); },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call3 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call4 _f) {
                _stack.push_back(_Call5{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call5 _f) { _result = f2(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call6 _f) {
                _stack.push_back(
                    _Call7{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call7 _f) {
                _stack.push_back(
                    _Call8{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call8 _f) {
                _result = f3(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<expr>, T1> F1,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F3,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1,
                   std::shared_ptr<expr>, T1>
                F4>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                     const std::shared_ptr<expr> &e) {
    struct _Enter {
      const std::shared_ptr<expr> e;
    };

    struct _Call1 {
      decltype(std::declval<const typename expr::Succ &>().d_a0) _s0;
    };

    struct _Call2 {
      decltype(std::declval<const typename expr::Add &>().d_a0) _s0;
      decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
    };

    struct _Call3 {
      T1 _s0;
      decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
    };

    struct _Call4 {
      decltype(std::declval<const typename expr::Mul &>().d_a0) _s0;
      decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
    };

    struct _Call5 {
      T1 _s0;
      decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
      decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
    };

    struct _Call6 {
      const std::shared_ptr<expr> _s0;
      const std::shared_ptr<expr> _s1;
      decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
    };

    struct _Call7 {
      T1 _s0;
      const std::shared_ptr<expr> _s1;
      decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
    };

    struct _Call8 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5,
                                _Call6, _Call7, _Call8>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{e});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<expr> e = _f.e;
                std::visit(
                    Overloaded{[&](const typename expr::Val _args) -> void {
                                 _result = f(_args.d_a0);
                               },
                               [&](const typename expr::Succ _args) -> void {
                                 _stack.push_back(_Call1{_args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a0});
                               },
                               [&](const typename expr::Add _args) -> void {
                                 _stack.push_back(_Call2{_args.d_a0, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               },
                               [&](const typename expr::Mul _args) -> void {
                                 _stack.push_back(_Call4{_args.d_a0, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a1});
                               },
                               [&](const typename expr::Cond _args) -> void {
                                 _stack.push_back(_Call6{_args.d_a1, _args.d_a0,
                                                         _args.d_a2, _args.d_a1,
                                                         _args.d_a0});
                                 _stack.push_back(_Enter{_args.d_a2});
                               }},
                    e->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s0, _result); },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call3 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call4 _f) {
                _stack.push_back(_Call5{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call5 _f) { _result = f2(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call6 _f) {
                _stack.push_back(
                    _Call7{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call7 _f) {
                _stack.push_back(
                    _Call8{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call8 _f) {
                _result = f3(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// eval e evaluates an expression. Multi-constructor recursion.
  __attribute__((pure)) static unsigned int
  eval(const std::shared_ptr<expr> &e);
  /// depth e computes expression depth.
  __attribute__((pure)) static unsigned int
  depth(const std::shared_ptr<expr> &e);
  /// count_vals e counts the number of Val nodes.
  __attribute__((pure)) static unsigned int
  count_vals(const std::shared_ptr<expr> &e);
  /// size e counts total number of nodes.
  __attribute__((pure)) static unsigned int
  size(const std::shared_ptr<expr> &e);
  /// simplify e performs algebraic simplification:
  /// Add(x, Val 0) = x, Add(Val 0, x) = x,
  /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
  /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
  static std::shared_ptr<expr> simplify(const std::shared_ptr<expr> &e);

  /// Alternative expression type for testing different evaluation strategy.
  struct simple_expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Plus {
      std::shared_ptr<simple_expr> d_a0;
      std::shared_ptr<simple_expr> d_a1;
    };

    struct IfPos {
      std::shared_ptr<simple_expr> d_a0;
      std::shared_ptr<simple_expr> d_a1;
      std::shared_ptr<simple_expr> d_a2;
    };

    using variant_t = std::variant<Lit, Plus, IfPos>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit simple_expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(Plus _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(IfPos _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<simple_expr> Lit_(unsigned int a0) {
        return std::shared_ptr<simple_expr>(new simple_expr(Lit{a0}));
      }

      static std::shared_ptr<simple_expr>
      Plus_(const std::shared_ptr<simple_expr> &a0,
            const std::shared_ptr<simple_expr> &a1) {
        return std::shared_ptr<simple_expr>(new simple_expr(Plus{a0, a1}));
      }

      static std::shared_ptr<simple_expr>
      IfPos_(const std::shared_ptr<simple_expr> &a0,
             const std::shared_ptr<simple_expr> &a1,
             const std::shared_ptr<simple_expr> &a2) {
        return std::shared_ptr<simple_expr>(new simple_expr(IfPos{a0, a1, a2}));
      }

      static std::unique_ptr<simple_expr> Lit_uptr(unsigned int a0) {
        return std::unique_ptr<simple_expr>(new simple_expr(Lit{a0}));
      }

      static std::unique_ptr<simple_expr>
      Plus_uptr(const std::shared_ptr<simple_expr> &a0,
                const std::shared_ptr<simple_expr> &a1) {
        return std::unique_ptr<simple_expr>(new simple_expr(Plus{a0, a1}));
      }

      static std::unique_ptr<simple_expr>
      IfPos_uptr(const std::shared_ptr<simple_expr> &a0,
                 const std::shared_ptr<simple_expr> &a1,
                 const std::shared_ptr<simple_expr> &a2) {
        return std::unique_ptr<simple_expr>(new simple_expr(IfPos{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<simple_expr>, T1, std::shared_ptr<simple_expr>,
             T1>
          F1,
      MapsTo<T1, std::shared_ptr<simple_expr>, T1, std::shared_ptr<simple_expr>,
             T1, std::shared_ptr<simple_expr>, T1>
          F2>
  static T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1,
                             const std::shared_ptr<simple_expr> &s) {
    struct _Enter {
      const std::shared_ptr<simple_expr> s;
    };

    struct _Call1 {
      decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s0;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
    };

    struct _Call3 {
      const std::shared_ptr<simple_expr> _s0;
      const std::shared_ptr<simple_expr> _s1;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
    };

    struct _Call4 {
      T1 _s0;
      const std::shared_ptr<simple_expr> _s1;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
    };

    struct _Call5 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{s});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<simple_expr> s = _f.s;
                std::visit(
                    Overloaded{
                        [&](const typename simple_expr::Lit _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename simple_expr::Plus _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename simple_expr::IfPos _args) -> void {
                          _stack.push_back(_Call3{_args.d_a1, _args.d_a0,
                                                  _args.d_a2, _args.d_a1,
                                                  _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    s->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f0(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(
                    _Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) {
                _stack.push_back(
                    _Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call5 _f) {
                _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<simple_expr>, T1, std::shared_ptr<simple_expr>,
             T1>
          F1,
      MapsTo<T1, std::shared_ptr<simple_expr>, T1, std::shared_ptr<simple_expr>,
             T1, std::shared_ptr<simple_expr>, T1>
          F2>
  static T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1,
                            const std::shared_ptr<simple_expr> &s) {
    struct _Enter {
      const std::shared_ptr<simple_expr> s;
    };

    struct _Call1 {
      decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s0;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
      decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
    };

    struct _Call3 {
      const std::shared_ptr<simple_expr> _s0;
      const std::shared_ptr<simple_expr> _s1;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
    };

    struct _Call4 {
      T1 _s0;
      const std::shared_ptr<simple_expr> _s1;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
    };

    struct _Call5 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
      decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{s});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<simple_expr> s = _f.s;
                std::visit(
                    Overloaded{
                        [&](const typename simple_expr::Lit _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename simple_expr::Plus _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename simple_expr::IfPos _args) -> void {
                          _stack.push_back(_Call3{_args.d_a1, _args.d_a0,
                                                  _args.d_a2, _args.d_a1,
                                                  _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    s->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f0(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(
                    _Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) {
                _stack.push_back(
                    _Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call5 _f) {
                _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// eval_simple e evaluates simple expression with positive test.
  __attribute__((pure)) static unsigned int
  eval_simple(const std::shared_ptr<simple_expr> &e);
  /// depth_simple e computes depth of simple expression tree.
  __attribute__((pure)) static unsigned int
  depth_simple(const std::shared_ptr<simple_expr> &e);

  /// Shape type demonstrating or-pattern matching.
  struct shape {
    // TYPES
    struct Circle {
      unsigned int d_a0;
    };

    struct Square {
      unsigned int d_a0;
    };

    struct Triangle {
      unsigned int d_a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<shape> Circle_(unsigned int a0) {
        return std::shared_ptr<shape>(new shape(Circle{a0}));
      }

      static std::shared_ptr<shape> Square_(unsigned int a0) {
        return std::shared_ptr<shape>(new shape(Square{a0}));
      }

      static std::shared_ptr<shape> Triangle_(unsigned int a0) {
        return std::shared_ptr<shape>(new shape(Triangle{a0}));
      }

      static std::unique_ptr<shape> Circle_uptr(unsigned int a0) {
        return std::unique_ptr<shape>(new shape(Circle{a0}));
      }

      static std::unique_ptr<shape> Square_uptr(unsigned int a0) {
        return std::unique_ptr<shape>(new shape(Square{a0}));
      }

      static std::unique_ptr<shape> Triangle_uptr(unsigned int a0) {
        return std::unique_ptr<shape>(new shape(Triangle{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1,
                       const std::shared_ptr<shape> &s) {
    return std::visit(
        Overloaded{[&](const typename shape::Circle _args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename shape::Square _args) -> T1 {
                     return f0(_args.d_a0);
                   },
                   [&](const typename shape::Triangle _args) -> T1 {
                     return f1(_args.d_a0);
                   }},
        s->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
  static T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<shape> &s) {
    return std::visit(
        Overloaded{[&](const typename shape::Circle _args) -> T1 {
                     return f(_args.d_a0);
                   },
                   [&](const typename shape::Square _args) -> T1 {
                     return f0(_args.d_a0);
                   },
                   [&](const typename shape::Triangle _args) -> T1 {
                     return f1(_args.d_a0);
                   }},
        s->v());
  }

  /// sum_shapes l sums values from shapes using unified pattern.
  /// Tests or-pattern style matching in Coq.
  __attribute__((pure)) static unsigned int
  sum_shapes(const std::shared_ptr<List<std::shared_ptr<shape>>> &l);
  /// count_by_shape l counts shapes: (circles, squares, triangles).
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  count_by_shape(const std::shared_ptr<List<std::shared_ptr<shape>>> &l);

  /// Alternative expression type with conditionals for testing different
  /// evaluation patterns.
  struct cond_expr {
    // TYPES
    struct CLit {
      unsigned int d_a0;
    };

    struct CPlus {
      std::shared_ptr<cond_expr> d_a0;
      std::shared_ptr<cond_expr> d_a1;
    };

    struct CCond {
      std::shared_ptr<cond_expr> d_a0;
      std::shared_ptr<cond_expr> d_a1;
      std::shared_ptr<cond_expr> d_a2;
    };

    using variant_t = std::variant<CLit, CPlus, CCond>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit cond_expr(CLit _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CPlus _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CCond _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<cond_expr> CLit_(unsigned int a0) {
        return std::shared_ptr<cond_expr>(new cond_expr(CLit{a0}));
      }

      static std::shared_ptr<cond_expr>
      CPlus_(const std::shared_ptr<cond_expr> &a0,
             const std::shared_ptr<cond_expr> &a1) {
        return std::shared_ptr<cond_expr>(new cond_expr(CPlus{a0, a1}));
      }

      static std::shared_ptr<cond_expr>
      CCond_(const std::shared_ptr<cond_expr> &a0,
             const std::shared_ptr<cond_expr> &a1,
             const std::shared_ptr<cond_expr> &a2) {
        return std::shared_ptr<cond_expr>(new cond_expr(CCond{a0, a1, a2}));
      }

      static std::unique_ptr<cond_expr> CLit_uptr(unsigned int a0) {
        return std::unique_ptr<cond_expr>(new cond_expr(CLit{a0}));
      }

      static std::unique_ptr<cond_expr>
      CPlus_uptr(const std::shared_ptr<cond_expr> &a0,
                 const std::shared_ptr<cond_expr> &a1) {
        return std::unique_ptr<cond_expr>(new cond_expr(CPlus{a0, a1}));
      }

      static std::unique_ptr<cond_expr>
      CCond_uptr(const std::shared_ptr<cond_expr> &a0,
                 const std::shared_ptr<cond_expr> &a1,
                 const std::shared_ptr<cond_expr> &a2) {
        return std::unique_ptr<cond_expr>(new cond_expr(CCond{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>, T1>
          F1,
      MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>, T1,
             std::shared_ptr<cond_expr>, T1>
          F2>
  static T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1,
                           const std::shared_ptr<cond_expr> &c) {
    struct _Enter {
      const std::shared_ptr<cond_expr> c;
    };

    struct _Call1 {
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s0;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
    };

    struct _Call3 {
      const std::shared_ptr<cond_expr> _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
    };

    struct _Call4 {
      T1 _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
    };

    struct _Call5 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{c});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<cond_expr> c = _f.c;
                std::visit(
                    Overloaded{
                        [&](const typename cond_expr::CLit _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename cond_expr::CPlus _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename cond_expr::CCond _args) -> void {
                          _stack.push_back(_Call3{_args.d_a1, _args.d_a0,
                                                  _args.d_a2, _args.d_a1,
                                                  _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    c->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f0(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(
                    _Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) {
                _stack.push_back(
                    _Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call5 _f) {
                _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>, T1>
          F1,
      MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>, T1,
             std::shared_ptr<cond_expr>, T1>
          F2>
  static T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1,
                          const std::shared_ptr<cond_expr> &c) {
    struct _Enter {
      const std::shared_ptr<cond_expr> c;
    };

    struct _Call1 {
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s0;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
    };

    struct _Call3 {
      const std::shared_ptr<cond_expr> _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
    };

    struct _Call4 {
      T1 _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
    };

    struct _Call5 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{c});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<cond_expr> c = _f.c;
                std::visit(
                    Overloaded{
                        [&](const typename cond_expr::CLit _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename cond_expr::CPlus _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename cond_expr::CCond _args) -> void {
                          _stack.push_back(_Call3{_args.d_a1, _args.d_a0,
                                                  _args.d_a2, _args.d_a1,
                                                  _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a2});
                        }},
                    c->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f0(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(
                    _Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) {
                _stack.push_back(
                    _Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
                _stack.push_back(_Enter{_f._s1});
              },
              [&](_Call5 _f) {
                _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  /// eval_cond e evaluates conditional expression.
  __attribute__((pure)) static unsigned int
  eval_cond(const std::shared_ptr<cond_expr> &e);

  /// depth_cond e computes depth of conditional expression tree.
  __attribute__((pure)) static unsigned int
  depth_cond(const std::shared_ptr<cond_expr> &e);
};

#endif // INCLUDED_LOOPIFY_EXPR
