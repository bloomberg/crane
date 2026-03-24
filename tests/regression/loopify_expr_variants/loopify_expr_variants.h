#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

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

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    std::shared_ptr<List<t_A>> _head{};
    std::shared_ptr<List<t_A>> _last{};
    const List *_loop_self = this;
    std::shared_ptr<List<t_A>> _loop_m = m;
    bool _continue = true;
    while (_continue) {
      std::visit(
          Overloaded{
              [&](const typename List<t_A>::Nil _args) {
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _loop_m;
                } else {
                  _head = _loop_m;
                }
                _continue = false;
              },
              [&](const typename List<t_A>::Cons _args) {
                auto _cell = List<t_A>::ctor::Cons_(_args.d_a0, nullptr);
                if (_last) {
                  std::get<typename List<t_A>::Cons>(_last->v_mut()).d_a1 =
                      _cell;
                } else {
                  _head = _cell;
                }
                _last = _cell;
                List *_next_self = _loop_m.get();
                std::shared_ptr<List<t_A>> _next_m = _args.d_a1;
                _loop_self = std::move(_next_self);
                _loop_m = std::move(_next_m);
              }},
          _loop_self->v());
    }
    return _head;
  }
};

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x, const unsigned int n);
};

struct LoopifyExprVariants {
  struct cond_expr {
    // TYPES
    struct Lit {
      unsigned int d_a0;
    };

    struct Add {
      std::shared_ptr<cond_expr> d_a0;
      std::shared_ptr<cond_expr> d_a1;
    };

    struct Cond {
      std::shared_ptr<cond_expr> d_a0;
      std::shared_ptr<cond_expr> d_a1;
      std::shared_ptr<cond_expr> d_a2;
    };

    using variant_t = std::variant<Lit, Add, Cond>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit cond_expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(Add _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(Cond _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<cond_expr> Lit_(unsigned int a0) {
        return std::shared_ptr<cond_expr>(new cond_expr(Lit{a0}));
      }

      static std::shared_ptr<cond_expr>
      Add_(const std::shared_ptr<cond_expr> &a0,
           const std::shared_ptr<cond_expr> &a1) {
        return std::shared_ptr<cond_expr>(new cond_expr(Add{a0, a1}));
      }

      static std::shared_ptr<cond_expr>
      Cond_(const std::shared_ptr<cond_expr> &a0,
            const std::shared_ptr<cond_expr> &a1,
            const std::shared_ptr<cond_expr> &a2) {
        return std::shared_ptr<cond_expr>(new cond_expr(Cond{a0, a1, a2}));
      }

      static std::unique_ptr<cond_expr> Lit_uptr(unsigned int a0) {
        return std::unique_ptr<cond_expr>(new cond_expr(Lit{a0}));
      }

      static std::unique_ptr<cond_expr>
      Add_uptr(const std::shared_ptr<cond_expr> &a0,
               const std::shared_ptr<cond_expr> &a1) {
        return std::unique_ptr<cond_expr>(new cond_expr(Add{a0, a1}));
      }

      static std::unique_ptr<cond_expr>
      Cond_uptr(const std::shared_ptr<cond_expr> &a0,
                const std::shared_ptr<cond_expr> &a1,
                const std::shared_ptr<cond_expr> &a2) {
        return std::unique_ptr<cond_expr>(new cond_expr(Cond{a0, a1, a2}));
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
      decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s0;
      decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
    };

    struct _Call3 {
      const std::shared_ptr<cond_expr> _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
    };

    struct _Call4 {
      T1 _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
    };

    struct _Call5 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
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
                        [&](const typename cond_expr::Lit _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename cond_expr::Add _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename cond_expr::Cond _args) -> void {
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
      decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s0;
      decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename cond_expr::Add &>().d_a1) _s1;
      decltype(std::declval<const typename cond_expr::Add &>().d_a0) _s2;
    };

    struct _Call3 {
      const std::shared_ptr<cond_expr> _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
    };

    struct _Call4 {
      T1 _s0;
      const std::shared_ptr<cond_expr> _s1;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
    };

    struct _Call5 {
      T1 _s0;
      T1 _s1;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a2) _s2;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a1) _s3;
      decltype(std::declval<const typename cond_expr::Cond &>().d_a0) _s4;
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
                        [&](const typename cond_expr::Lit _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename cond_expr::Add _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename cond_expr::Cond _args) -> void {
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

  __attribute__((pure)) static unsigned int
  eval_cond(const std::shared_ptr<cond_expr> &e);
  __attribute__((pure)) static unsigned int
  size_cond(const std::shared_ptr<cond_expr> &e);

  struct arith_expr {
    // TYPES
    struct ANum {
      unsigned int d_a0;
    };

    struct AAdd {
      std::shared_ptr<arith_expr> d_a0;
      std::shared_ptr<arith_expr> d_a1;
    };

    struct AMul {
      std::shared_ptr<arith_expr> d_a0;
      std::shared_ptr<arith_expr> d_a1;
    };

    struct ADiv {
      std::shared_ptr<arith_expr> d_a0;
      std::shared_ptr<arith_expr> d_a1;
    };

    using variant_t = std::variant<ANum, AAdd, AMul, ADiv>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit arith_expr(ANum _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(AAdd _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(AMul _v) : d_v_(std::move(_v)) {}

    explicit arith_expr(ADiv _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<arith_expr> ANum_(unsigned int a0) {
        return std::shared_ptr<arith_expr>(new arith_expr(ANum{a0}));
      }

      static std::shared_ptr<arith_expr>
      AAdd_(const std::shared_ptr<arith_expr> &a0,
            const std::shared_ptr<arith_expr> &a1) {
        return std::shared_ptr<arith_expr>(new arith_expr(AAdd{a0, a1}));
      }

      static std::shared_ptr<arith_expr>
      AMul_(const std::shared_ptr<arith_expr> &a0,
            const std::shared_ptr<arith_expr> &a1) {
        return std::shared_ptr<arith_expr>(new arith_expr(AMul{a0, a1}));
      }

      static std::shared_ptr<arith_expr>
      ADiv_(const std::shared_ptr<arith_expr> &a0,
            const std::shared_ptr<arith_expr> &a1) {
        return std::shared_ptr<arith_expr>(new arith_expr(ADiv{a0, a1}));
      }

      static std::unique_ptr<arith_expr> ANum_uptr(unsigned int a0) {
        return std::unique_ptr<arith_expr>(new arith_expr(ANum{a0}));
      }

      static std::unique_ptr<arith_expr>
      AAdd_uptr(const std::shared_ptr<arith_expr> &a0,
                const std::shared_ptr<arith_expr> &a1) {
        return std::unique_ptr<arith_expr>(new arith_expr(AAdd{a0, a1}));
      }

      static std::unique_ptr<arith_expr>
      AMul_uptr(const std::shared_ptr<arith_expr> &a0,
                const std::shared_ptr<arith_expr> &a1) {
        return std::unique_ptr<arith_expr>(new arith_expr(AMul{a0, a1}));
      }

      static std::unique_ptr<arith_expr>
      ADiv_uptr(const std::shared_ptr<arith_expr> &a0,
                const std::shared_ptr<arith_expr> &a1) {
        return std::unique_ptr<arith_expr>(new arith_expr(ADiv{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                   std::shared_ptr<arith_expr>, T1>
                F1,
            MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                   std::shared_ptr<arith_expr>, T1>
                F2,
            MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                   std::shared_ptr<arith_expr>, T1>
                F3>
  static T1 arith_expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2,
                            const std::shared_ptr<arith_expr> &a) {
    struct _Enter {
      const std::shared_ptr<arith_expr> a;
    };

    struct _Call1 {
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s0;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
    };

    struct _Call3 {
      decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s0;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
    };

    struct _Call4 {
      T1 _s0;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
    };

    struct _Call5 {
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s0;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
    };

    struct _Call6 {
      T1 _s0;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
    };

    using _Frame =
        std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{a});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<arith_expr> a = _f.a;
                std::visit(
                    Overloaded{
                        [&](const typename arith_expr::ANum _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename arith_expr::AAdd _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename arith_expr::AMul _args) -> void {
                          _stack.push_back(
                              _Call3{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename arith_expr::ADiv _args) -> void {
                          _stack.push_back(
                              _Call5{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    a->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f0(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call5 _f) {
                _stack.push_back(_Call6{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call6 _f) {
                _result = f2(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                   std::shared_ptr<arith_expr>, T1>
                F1,
            MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                   std::shared_ptr<arith_expr>, T1>
                F2,
            MapsTo<T1, std::shared_ptr<arith_expr>, T1,
                   std::shared_ptr<arith_expr>, T1>
                F3>
  static T1 arith_expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2,
                           const std::shared_ptr<arith_expr> &a) {
    struct _Enter {
      const std::shared_ptr<arith_expr> a;
    };

    struct _Call1 {
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s0;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AAdd &>().d_a0) _s2;
    };

    struct _Call3 {
      decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s0;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
    };

    struct _Call4 {
      T1 _s0;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::AMul &>().d_a0) _s2;
    };

    struct _Call5 {
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s0;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
    };

    struct _Call6 {
      T1 _s0;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a1) _s1;
      decltype(std::declval<const typename arith_expr::ADiv &>().d_a0) _s2;
    };

    using _Frame =
        std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{a});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<arith_expr> a = _f.a;
                std::visit(
                    Overloaded{
                        [&](const typename arith_expr::ANum _args) -> void {
                          _result = f(_args.d_a0);
                        },
                        [&](const typename arith_expr::AAdd _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename arith_expr::AMul _args) -> void {
                          _stack.push_back(
                              _Call3{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename arith_expr::ADiv _args) -> void {
                          _stack.push_back(
                              _Call5{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        }},
                    a->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f0(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call5 _f) {
                _stack.push_back(_Call6{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call6 _f) {
                _result = f2(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static unsigned int
  eval_arith(const std::shared_ptr<arith_expr> &e);
  __attribute__((pure)) static unsigned int
  count_ops(const std::shared_ptr<arith_expr> &e);

  struct bool_expr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<bool_expr> d_a0;
      std::shared_ptr<bool_expr> d_a1;
    };

    struct BOr {
      std::shared_ptr<bool_expr> d_a0;
      std::shared_ptr<bool_expr> d_a1;
    };

    struct BNot {
      std::shared_ptr<bool_expr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit bool_expr(BTrue _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BFalse _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BOr _v) : d_v_(std::move(_v)) {}

    explicit bool_expr(BNot _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<bool_expr> BTrue_() {
        return std::shared_ptr<bool_expr>(new bool_expr(BTrue{}));
      }

      static std::shared_ptr<bool_expr> BFalse_() {
        return std::shared_ptr<bool_expr>(new bool_expr(BFalse{}));
      }

      static std::shared_ptr<bool_expr>
      BAnd_(const std::shared_ptr<bool_expr> &a0,
            const std::shared_ptr<bool_expr> &a1) {
        return std::shared_ptr<bool_expr>(new bool_expr(BAnd{a0, a1}));
      }

      static std::shared_ptr<bool_expr>
      BOr_(const std::shared_ptr<bool_expr> &a0,
           const std::shared_ptr<bool_expr> &a1) {
        return std::shared_ptr<bool_expr>(new bool_expr(BOr{a0, a1}));
      }

      static std::shared_ptr<bool_expr>
      BNot_(const std::shared_ptr<bool_expr> &a0) {
        return std::shared_ptr<bool_expr>(new bool_expr(BNot{a0}));
      }

      static std::unique_ptr<bool_expr> BTrue_uptr() {
        return std::unique_ptr<bool_expr>(new bool_expr(BTrue{}));
      }

      static std::unique_ptr<bool_expr> BFalse_uptr() {
        return std::unique_ptr<bool_expr>(new bool_expr(BFalse{}));
      }

      static std::unique_ptr<bool_expr>
      BAnd_uptr(const std::shared_ptr<bool_expr> &a0,
                const std::shared_ptr<bool_expr> &a1) {
        return std::unique_ptr<bool_expr>(new bool_expr(BAnd{a0, a1}));
      }

      static std::unique_ptr<bool_expr>
      BOr_uptr(const std::shared_ptr<bool_expr> &a0,
               const std::shared_ptr<bool_expr> &a1) {
        return std::unique_ptr<bool_expr>(new bool_expr(BOr{a0, a1}));
      }

      static std::unique_ptr<bool_expr>
      BNot_uptr(const std::shared_ptr<bool_expr> &a0) {
        return std::unique_ptr<bool_expr>(new bool_expr(BNot{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F2,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F3,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1> F4>
  static T1 bool_expr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                           const std::shared_ptr<bool_expr> &b) {
    struct _Enter {
      const std::shared_ptr<bool_expr> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call3 {
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call4 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call5 {
      decltype(std::declval<const typename bool_expr::BNot &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<bool_expr> b = _f.b;
                std::visit(
                    Overloaded{
                        [&](const typename bool_expr::BTrue _args) -> void {
                          _result = f;
                        },
                        [&](const typename bool_expr::BFalse _args) -> void {
                          _result = f0;
                        },
                        [&](const typename bool_expr::BAnd _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BOr _args) -> void {
                          _stack.push_back(
                              _Call3{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BNot _args) -> void {
                          _stack.push_back(_Call5{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a0});
                        }},
                    b->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) { _result = f2(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call5 _f) { _result = f3(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F2,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1, std::shared_ptr<bool_expr>, T1>
          F3,
      MapsTo<T1, std::shared_ptr<bool_expr>, T1> F4>
  static T1 bool_expr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                          const std::shared_ptr<bool_expr> &b) {
    struct _Enter {
      const std::shared_ptr<bool_expr> b;
    };

    struct _Call1 {
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call2 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BAnd &>().d_a0) _s2;
    };

    struct _Call3 {
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call4 {
      T1 _s0;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a1) _s1;
      decltype(std::declval<const typename bool_expr::BOr &>().d_a0) _s2;
    };

    struct _Call5 {
      decltype(std::declval<const typename bool_expr::BNot &>().d_a0) _s0;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{b});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<bool_expr> b = _f.b;
                std::visit(
                    Overloaded{
                        [&](const typename bool_expr::BTrue _args) -> void {
                          _result = f;
                        },
                        [&](const typename bool_expr::BFalse _args) -> void {
                          _result = f0;
                        },
                        [&](const typename bool_expr::BAnd _args) -> void {
                          _stack.push_back(
                              _Call1{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BOr _args) -> void {
                          _stack.push_back(
                              _Call3{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename bool_expr::BNot _args) -> void {
                          _stack.push_back(_Call5{_args.d_a0});
                          _stack.push_back(_Enter{_args.d_a0});
                        }},
                    b->v());
              },
              [&](_Call1 _f) {
                _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call2 _f) { _result = f1(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call3 _f) {
                _stack.push_back(_Call4{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call4 _f) { _result = f2(_f._s2, _result, _f._s1, _f._s0); },
              [&](_Call5 _f) { _result = f3(_f._s0, _result); }},
          _frame);
    }
    return _result;
  }

  __attribute__((pure)) static bool
  eval_bool(const std::shared_ptr<bool_expr> &e);
  static std::shared_ptr<bool_expr>
  simplify_bool(const std::shared_ptr<bool_expr> &e);

  struct list_expr {
    // TYPES
    struct LNil {};

    struct LCons {
      unsigned int d_a0;
      std::shared_ptr<list_expr> d_a1;
    };

    struct LAppend {
      std::shared_ptr<list_expr> d_a0;
      std::shared_ptr<list_expr> d_a1;
    };

    struct LReplicate {
      unsigned int d_a0;
      unsigned int d_a1;
    };

    using variant_t = std::variant<LNil, LCons, LAppend, LReplicate>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit list_expr(LNil _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LCons _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LAppend _v) : d_v_(std::move(_v)) {}

    explicit list_expr(LReplicate _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<list_expr> LNil_() {
        return std::shared_ptr<list_expr>(new list_expr(LNil{}));
      }

      static std::shared_ptr<list_expr>
      LCons_(unsigned int a0, const std::shared_ptr<list_expr> &a1) {
        return std::shared_ptr<list_expr>(new list_expr(LCons{a0, a1}));
      }

      static std::shared_ptr<list_expr>
      LAppend_(const std::shared_ptr<list_expr> &a0,
               const std::shared_ptr<list_expr> &a1) {
        return std::shared_ptr<list_expr>(new list_expr(LAppend{a0, a1}));
      }

      static std::shared_ptr<list_expr> LReplicate_(unsigned int a0,
                                                    unsigned int a1) {
        return std::shared_ptr<list_expr>(new list_expr(LReplicate{a0, a1}));
      }

      static std::unique_ptr<list_expr> LNil_uptr() {
        return std::unique_ptr<list_expr>(new list_expr(LNil{}));
      }

      static std::unique_ptr<list_expr>
      LCons_uptr(unsigned int a0, const std::shared_ptr<list_expr> &a1) {
        return std::unique_ptr<list_expr>(new list_expr(LCons{a0, a1}));
      }

      static std::unique_ptr<list_expr>
      LAppend_uptr(const std::shared_ptr<list_expr> &a0,
                   const std::shared_ptr<list_expr> &a1) {
        return std::unique_ptr<list_expr>(new list_expr(LAppend{a0, a1}));
      }

      static std::unique_ptr<list_expr> LReplicate_uptr(unsigned int a0,
                                                        unsigned int a1) {
        return std::unique_ptr<list_expr>(new list_expr(LReplicate{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int, std::shared_ptr<list_expr>, T1> F1,
      MapsTo<T1, std::shared_ptr<list_expr>, T1, std::shared_ptr<list_expr>, T1>
          F2,
      MapsTo<T1, unsigned int, unsigned int> F3>
  static T1 list_expr_rect(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2,
                           const std::shared_ptr<list_expr> &l) {
    struct _Enter {
      const std::shared_ptr<list_expr> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list_expr::LCons &>().d_a1) _s0;
      decltype(std::declval<const typename list_expr::LCons &>().d_a0) _s1;
    };

    struct _Call2 {
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    struct _Call3 {
      T1 _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list_expr> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list_expr::LNil _args) -> void {
                          _result = f;
                        },
                        [&](const typename list_expr::LCons _args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LAppend _args) -> void {
                          _stack.push_back(
                              _Call2{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LReplicate _args)
                            -> void { _result = f2(_args.d_a0, _args.d_a1); }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call3 _f) {
                _result = f1(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  template <
      typename T1, MapsTo<T1, unsigned int, std::shared_ptr<list_expr>, T1> F1,
      MapsTo<T1, std::shared_ptr<list_expr>, T1, std::shared_ptr<list_expr>, T1>
          F2,
      MapsTo<T1, unsigned int, unsigned int> F3>
  static T1 list_expr_rec(const T1 f, F1 &&f0, F2 &&f1, F3 &&f2,
                          const std::shared_ptr<list_expr> &l) {
    struct _Enter {
      const std::shared_ptr<list_expr> l;
    };

    struct _Call1 {
      decltype(std::declval<const typename list_expr::LCons &>().d_a1) _s0;
      decltype(std::declval<const typename list_expr::LCons &>().d_a0) _s1;
    };

    struct _Call2 {
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    struct _Call3 {
      T1 _s0;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a1) _s1;
      decltype(std::declval<const typename list_expr::LAppend &>().d_a0) _s2;
    };

    using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.push_back(_Enter{l});
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      std::visit(
          Overloaded{
              [&](_Enter _f) {
                const std::shared_ptr<list_expr> l = _f.l;
                std::visit(
                    Overloaded{
                        [&](const typename list_expr::LNil _args) -> void {
                          _result = f;
                        },
                        [&](const typename list_expr::LCons _args) -> void {
                          _stack.push_back(_Call1{_args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LAppend _args) -> void {
                          _stack.push_back(
                              _Call2{_args.d_a0, _args.d_a1, _args.d_a0});
                          _stack.push_back(_Enter{_args.d_a1});
                        },
                        [&](const typename list_expr::LReplicate _args)
                            -> void { _result = f2(_args.d_a0, _args.d_a1); }},
                    l->v());
              },
              [&](_Call1 _f) { _result = f0(_f._s1, _f._s0, _result); },
              [&](_Call2 _f) {
                _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                _stack.push_back(_Enter{_f._s0});
              },
              [&](_Call3 _f) {
                _result = f1(_f._s2, _result, _f._s1, _f._s0);
              }},
          _frame);
    }
    return _result;
  }

  static std::shared_ptr<List<unsigned int>>
  eval_list(const std::shared_ptr<list_expr> &e);
  __attribute__((pure)) static unsigned int
  list_expr_size(const std::shared_ptr<list_expr> &e);
};

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x, const unsigned int n) {
  std::shared_ptr<List<T1>> _head{};
  std::shared_ptr<List<T1>> _last{};
  unsigned int _loop_n = n;
  bool _continue = true;
  while (_continue) {
    if (_loop_n <= 0) {
      {
        if (_last) {
          std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 =
              List<T1>::ctor::Nil_();
        } else {
          _head = List<T1>::ctor::Nil_();
        }
        _continue = false;
      }
    } else {
      unsigned int k = _loop_n - 1;
      {
        auto _cell = List<T1>::ctor::Cons_(x, nullptr);
        if (_last) {
          std::get<typename List<T1>::Cons>(_last->v_mut()).d_a1 = _cell;
        } else {
          _head = _cell;
        }
        _last = _cell;
        _loop_n = k;
        continue;
      }
    }
  }
  return _head;
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
