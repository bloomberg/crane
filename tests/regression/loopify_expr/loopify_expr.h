#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

#include <algorithm>
#include <memory>
#include <type_traits>
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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

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

  public:
    // CREATORS
    explicit expr(Val _v) : d_v_(std::move(_v)) {}

    explicit expr(Succ _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    explicit expr(Cond _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<expr> val(unsigned int a0) {
      return std::make_shared<expr>(Val{std::move(a0)});
    }

    static std::shared_ptr<expr> succ(const std::shared_ptr<expr> &a0) {
      return std::make_shared<expr>(Succ{a0});
    }

    static std::shared_ptr<expr> succ(std::shared_ptr<expr> &&a0) {
      return std::make_shared<expr>(Succ{std::move(a0)});
    }

    static std::shared_ptr<expr> add(const std::shared_ptr<expr> &a0,
                                     const std::shared_ptr<expr> &a1) {
      return std::make_shared<expr>(Add{a0, a1});
    }

    static std::shared_ptr<expr> add(std::shared_ptr<expr> &&a0,
                                     std::shared_ptr<expr> &&a1) {
      return std::make_shared<expr>(Add{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<expr> mul(const std::shared_ptr<expr> &a0,
                                     const std::shared_ptr<expr> &a1) {
      return std::make_shared<expr>(Mul{a0, a1});
    }

    static std::shared_ptr<expr> mul(std::shared_ptr<expr> &&a0,
                                     std::shared_ptr<expr> &&a1) {
      return std::make_shared<expr>(Mul{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<expr> cond(const std::shared_ptr<expr> &a0,
                                      const std::shared_ptr<expr> &a1,
                                      const std::shared_ptr<expr> &a2) {
      return std::make_shared<expr>(Cond{a0, a1, a2});
    }

    static std::shared_ptr<expr> cond(std::shared_ptr<expr> &&a0,
                                      std::shared_ptr<expr> &&a1,
                                      std::shared_ptr<expr> &&a2) {
      return std::make_shared<expr>(
          Cond{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<expr> val_uptr(unsigned int a0) {
      return std::make_unique<expr>(Val{std::move(a0)});
    }

    static std::unique_ptr<expr> succ_uptr(const std::shared_ptr<expr> &a0) {
      return std::make_unique<expr>(Succ{a0});
    }

    static std::unique_ptr<expr> succ_uptr(std::shared_ptr<expr> &&a0) {
      return std::make_unique<expr>(Succ{std::move(a0)});
    }

    static std::unique_ptr<expr> add_uptr(const std::shared_ptr<expr> &a0,
                                          const std::shared_ptr<expr> &a1) {
      return std::make_unique<expr>(Add{a0, a1});
    }

    static std::unique_ptr<expr> add_uptr(std::shared_ptr<expr> &&a0,
                                          std::shared_ptr<expr> &&a1) {
      return std::make_unique<expr>(Add{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<expr> mul_uptr(const std::shared_ptr<expr> &a0,
                                          const std::shared_ptr<expr> &a1) {
      return std::make_unique<expr>(Mul{a0, a1});
    }

    static std::unique_ptr<expr> mul_uptr(std::shared_ptr<expr> &&a0,
                                          std::shared_ptr<expr> &&a1) {
      return std::make_unique<expr>(Mul{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<expr> cond_uptr(const std::shared_ptr<expr> &a0,
                                           const std::shared_ptr<expr> &a1,
                                           const std::shared_ptr<expr> &a2) {
      return std::make_unique<expr>(Cond{a0, a1, a2});
    }

    static std::unique_ptr<expr> cond_uptr(std::shared_ptr<expr> &&a0,
                                           std::shared_ptr<expr> &&a1,
                                           std::shared_ptr<expr> &&a2) {
      return std::make_unique<expr>(
          Cond{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// simplify e performs algebraic simplification:
    /// Add(x, Val 0) = x, Add(Val 0, x) = x,
    /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
    std::shared_ptr<expr> simplify() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {};

      struct _Call10 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call11 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call12 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call13 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call14 {
        const expr *_s0;
        const expr *_s1;
      };

      struct _Call15 {
        std::shared_ptr<expr> _s0;
        const expr *_s1;
      };

      struct _Call16 {
        std::shared_ptr<expr> _s0;
        std::shared_ptr<expr> _s1;
      };

      struct _Call2 {
        const typename expr::Add _s0;
      };

      struct _Call3 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call4 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call5 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call6 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call7 {
        std::shared_ptr<expr> _s0;
      };

      struct _Call8 {
        const typename expr::Mul _s0;
      };

      struct _Call9 {
        const typename expr::Val _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call10, _Call11, _Call12, _Call13,
                       _Call14, _Call15, _Call16, _Call2, _Call3, _Call4,
                       _Call5, _Call6, _Call7, _Call8, _Call9>;
      std::shared_ptr<expr> _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const expr *_self = _f._self;
                  std::visit(
                      Overloaded{[&](const typename expr::Val _args) -> void {
                                   _result = expr::val(_args.d_a0);
                                 },
                                 [&](const typename expr::Succ _args) -> void {
                                   _stack.push_back(_Call1{});
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 },
                                 [&](const typename expr::Add _args) -> void {
                                   _stack.push_back(_Call2{_args});
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 },
                                 [&](const typename expr::Mul _args) -> void {
                                   _stack.push_back(_Call8{_args});
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 },
                                 [&](const typename expr::Cond _args) -> void {
                                   _stack.push_back(_Call14{_args.d_a1.get(),
                                                            _args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a2.get()});
                                 }},
                      _self->v());
                },
                [&](_Call1 _f) { _result = expr::succ(_result); },
                [&](_Call10 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = expr::val(0u);
                            } else {
                              unsigned int _x = _args1.d_a0 - 1;
                              if (std::move(_args1.d_a0) == 1u) {
                                _result = s1;
                              } else {
                                _result = expr::mul(
                                    s1, expr::val(std::move(_args1.d_a0)));
                              }
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::mul(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call11 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = expr::val(0u);
                            } else {
                              unsigned int _x = _args1.d_a0 - 1;
                              if (std::move(_args1.d_a0) == 1u) {
                                _result = s1;
                              } else {
                                _result = expr::mul(
                                    s1, expr::val(std::move(_args1.d_a0)));
                              }
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::mul(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call12 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = expr::val(0u);
                            } else {
                              unsigned int _x = _args1.d_a0 - 1;
                              if (std::move(_args1.d_a0) == 1u) {
                                _result = s1;
                              } else {
                                _result = expr::mul(
                                    s1, expr::val(std::move(_args1.d_a0)));
                              }
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::mul(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call13 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = expr::val(0u);
                            } else {
                              unsigned int _x = _args1.d_a0 - 1;
                              if (std::move(_args1.d_a0) == 1u) {
                                _result = s1;
                              } else {
                                _result = expr::mul(
                                    s1, expr::val(std::move(_args1.d_a0)));
                              }
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::mul(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::mul(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
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
                  _result = expr::cond(_result, _f._s1, _f._s0);
                },
                [&](_Call2 _f) {
                  const typename expr::Add _args = _f._s0;
                  std::visit(
                      Overloaded{[&](const typename expr::Val _args0) -> void {
                                   if (_args0.d_a0 <= 0) {
                                     _stack.push_back(_Enter{_args.d_a1.get()});
                                   } else {
                                     unsigned int n0 = _args0.d_a0 - 1;
                                     std::shared_ptr<expr> s1 =
                                         expr::val((n0 + 1));
                                     _stack.push_back(_Call3{s1});
                                     _stack.push_back(_Enter{_args.d_a1.get()});
                                   }
                                 },
                                 [&](const typename expr::Succ _args0) -> void {
                                   std::shared_ptr<expr> s1 =
                                       expr::succ(_args0.d_a0);
                                   _stack.push_back(_Call4{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Add _args0) -> void {
                                   std::shared_ptr<expr> s1 =
                                       expr::add(_args0.d_a0, _args0.d_a1);
                                   _stack.push_back(_Call5{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Mul _args0) -> void {
                                   std::shared_ptr<expr> s1 =
                                       expr::mul(_args0.d_a0, _args0.d_a1);
                                   _stack.push_back(_Call6{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Cond _args0) -> void {
                                   std::shared_ptr<expr> s1 = expr::cond(
                                       _args0.d_a0, _args0.d_a1, _args0.d_a2);
                                   _stack.push_back(_Call7{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 }},
                      _result->v());
                },
                [&](_Call3 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = std::move(s1);
                            } else {
                              unsigned int n2 = _args1.d_a0 - 1;
                              _result = expr::add(s1, expr::val((n2 + 1)));
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::add(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call4 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = std::move(s1);
                            } else {
                              unsigned int n0 = _args1.d_a0 - 1;
                              _result = expr::add(s1, expr::val((n0 + 1)));
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::add(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call5 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = std::move(s1);
                            } else {
                              unsigned int n0 = _args1.d_a0 - 1;
                              _result = expr::add(s1, expr::val((n0 + 1)));
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::add(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call6 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = std::move(s1);
                            } else {
                              unsigned int n0 = _args1.d_a0 - 1;
                              _result = expr::add(s1, expr::val((n0 + 1)));
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::add(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call7 _f) {
                  std::shared_ptr<expr> s1 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = std::move(s1);
                            } else {
                              unsigned int n0 = _args1.d_a0 - 1;
                              _result = expr::add(s1, expr::val((n0 + 1)));
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            _result = expr::add(std::move(s1),
                                                expr::succ(_args1.d_a0));
                          },
                          [&](const typename expr::Add _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::add(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::mul(_args1.d_a0, _args1.d_a1));
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            _result =
                                expr::add(std::move(s1),
                                          expr::cond(_args1.d_a0, _args1.d_a1,
                                                     _args1.d_a2));
                          }},
                      _result->v());
                },
                [&](_Call8 _f) {
                  const typename expr::Mul _args = _f._s0;
                  std::visit(
                      Overloaded{[&](const typename expr::Val _args0) -> void {
                                   if (_args0.d_a0 <= 0) {
                                     _result = expr::val(0u);
                                   } else {
                                     unsigned int _x = _args0.d_a0 - 1;
                                     _stack.push_back(_Call9{_args0});
                                     _stack.push_back(_Enter{_args.d_a1.get()});
                                   }
                                 },
                                 [&](const typename expr::Succ _args0) -> void {
                                   std::shared_ptr<expr> s1 =
                                       expr::succ(_args0.d_a0);
                                   _stack.push_back(_Call10{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Add _args0) -> void {
                                   std::shared_ptr<expr> s1 =
                                       expr::add(_args0.d_a0, _args0.d_a1);
                                   _stack.push_back(_Call11{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Mul _args0) -> void {
                                   std::shared_ptr<expr> s1 =
                                       expr::mul(_args0.d_a0, _args0.d_a1);
                                   _stack.push_back(_Call12{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Cond _args0) -> void {
                                   std::shared_ptr<expr> s1 = expr::cond(
                                       _args0.d_a0, _args0.d_a1, _args0.d_a2);
                                   _stack.push_back(_Call13{s1});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 }},
                      _result->v());
                },
                [&](_Call9 _f) {
                  const typename expr::Val _args0 = _f._s0;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args1) -> void {
                            if (_args1.d_a0 <= 0) {
                              _result = expr::val(0u);
                            } else {
                              unsigned int n1 = _args1.d_a0 - 1;
                              std::shared_ptr<expr> s2 = expr::val((n1 + 1));
                              if (_args0.d_a0 == 1u) {
                                _result = std::move(s2);
                              } else {
                                _result = expr::mul(expr::val(_args0.d_a0),
                                                    std::move(s2));
                              }
                            }
                          },
                          [&](const typename expr::Succ _args1) -> void {
                            std::shared_ptr<expr> s2 = expr::succ(_args1.d_a0);
                            if (_args0.d_a0 == 1u) {
                              _result = std::move(s2);
                            } else {
                              _result = expr::mul(expr::val(_args0.d_a0),
                                                  std::move(s2));
                            }
                          },
                          [&](const typename expr::Add _args1) -> void {
                            std::shared_ptr<expr> s2 =
                                expr::add(_args1.d_a0, _args1.d_a1);
                            if (_args0.d_a0 == 1u) {
                              _result = std::move(s2);
                            } else {
                              _result = expr::mul(expr::val(_args0.d_a0),
                                                  std::move(s2));
                            }
                          },
                          [&](const typename expr::Mul _args1) -> void {
                            std::shared_ptr<expr> s2 =
                                expr::mul(_args1.d_a0, _args1.d_a1);
                            if (_args0.d_a0 == 1u) {
                              _result = std::move(s2);
                            } else {
                              _result = expr::mul(expr::val(_args0.d_a0),
                                                  std::move(s2));
                            }
                          },
                          [&](const typename expr::Cond _args1) -> void {
                            std::shared_ptr<expr> s2 = expr::cond(
                                _args1.d_a0, _args1.d_a1, _args1.d_a2);
                            if (_args0.d_a0 == 1u) {
                              _result = std::move(s2);
                            } else {
                              _result = expr::mul(expr::val(_args0.d_a0),
                                                  std::move(s2));
                            }
                          }},
                      _result->v());
                }},
            _frame);
      }
      return _result;
    }

    /// size e counts total number of nodes.
    __attribute__((pure)) unsigned int size() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {};

      struct _Call2 {
        decltype(std::declval<const typename expr::Add &>().d_a0.get()) _s0;
      };

      struct _Call3 {
        unsigned int _s0;
      };

      struct _Call4 {
        decltype(std::declval<const typename expr::Mul &>().d_a0.get()) _s0;
      };

      struct _Call5 {
        unsigned int _s0;
      };

      struct _Call6 {
        const expr *_s0;
        const expr *_s1;
      };

      struct _Call7 {
        unsigned int _s0;
        const expr *_s1;
      };

      struct _Call8 {
        unsigned int _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4,
                                  _Call5, _Call6, _Call7, _Call8>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
                         const expr *_self = _f._self;
                         std::visit(
                             Overloaded{
                                 [&](const typename expr::Val _args) -> void {
                                   _result = 1u;
                                 },
                                 [&](const typename expr::Succ _args) -> void {
                                   _stack.push_back(_Call1{});
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 },
                                 [&](const typename expr::Add _args) -> void {
                                   _stack.push_back(_Call2{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Mul _args) -> void {
                                   _stack.push_back(_Call4{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Cond _args) -> void {
                                   _stack.push_back(_Call6{_args.d_a1.get(),
                                                           _args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a2.get()});
                                 }},
                             _self->v());
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
                       [&](_Call8 _f) {
                         _result = ((_result + (_f._s1 + _f._s0)) + 1);
                       }},
            _frame);
      }
      return _result;
    }

    /// count_vals e counts the number of Val nodes.
    __attribute__((pure)) unsigned int count_vals() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename expr::Add &>().d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        decltype(std::declval<const typename expr::Mul &>().d_a0.get()) _s0;
      };

      struct _Call4 {
        unsigned int _s0;
      };

      struct _Call5 {
        const expr *_s0;
        const expr *_s1;
      };

      struct _Call6 {
        unsigned int _s0;
        const expr *_s1;
      };

      struct _Call7 {
        unsigned int _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4,
                                  _Call5, _Call6, _Call7>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const expr *_self = _f._self;
                  std::visit(
                      Overloaded{[&](const typename expr::Val _args) -> void {
                                   _result = 1u;
                                 },
                                 [&](const typename expr::Succ _args) -> void {
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 },
                                 [&](const typename expr::Add _args) -> void {
                                   _stack.push_back(_Call1{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Mul _args) -> void {
                                   _stack.push_back(_Call3{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Cond _args) -> void {
                                   _stack.push_back(_Call5{_args.d_a1.get(),
                                                           _args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a2.get()});
                                 }},
                      _self->v());
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

    /// depth e computes expression depth.
    __attribute__((pure)) unsigned int depth() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {};

      struct _Call2 {
        decltype(std::declval<const typename expr::Add &>().d_a0.get()) _s0;
      };

      struct _Call3 {
        unsigned int _s0;
      };

      struct _Call4 {
        decltype(std::declval<const typename expr::Mul &>().d_a0.get()) _s0;
      };

      struct _Call5 {
        unsigned int _s0;
      };

      struct _Call6 {
        const expr *_s0;
        const expr *_s1;
      };

      struct _Call7 {
        unsigned int _s0;
        const expr *_s1;
      };

      struct _Call8 {
        unsigned int _s0;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4,
                                  _Call5, _Call6, _Call7, _Call8>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const expr *_self = _f._self;
                  std::visit(
                      Overloaded{[&](const typename expr::Val _args) -> void {
                                   _result = 0u;
                                 },
                                 [&](const typename expr::Succ _args) -> void {
                                   _stack.push_back(_Call1{});
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 },
                                 [&](const typename expr::Add _args) -> void {
                                   _stack.push_back(_Call2{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Mul _args) -> void {
                                   _stack.push_back(_Call4{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Cond _args) -> void {
                                   _stack.push_back(_Call6{_args.d_a1.get(),
                                                           _args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a2.get()});
                                 }},
                      _self->v());
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

    /// eval e evaluates an expression. Multi-constructor recursion.
    __attribute__((pure)) unsigned int eval() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {};

      struct _Call2 {
        decltype(std::declval<const typename expr::Add &>().d_a0.get()) _s0;
      };

      struct _Call3 {
        unsigned int _s0;
      };

      struct _Call4 {
        decltype(std::declval<const typename expr::Mul &>().d_a0.get()) _s0;
      };

      struct _Call5 {
        unsigned int _s0;
      };

      struct _Call6 {
        const typename expr::Cond _s0;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5, _Call6>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{[&](_Enter _f) {
                         const expr *_self = _f._self;
                         std::visit(
                             Overloaded{
                                 [&](const typename expr::Val _args) -> void {
                                   _result = _args.d_a0;
                                 },
                                 [&](const typename expr::Succ _args) -> void {
                                   _stack.push_back(_Call1{});
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 },
                                 [&](const typename expr::Add _args) -> void {
                                   _stack.push_back(_Call2{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Mul _args) -> void {
                                   _stack.push_back(_Call4{_args.d_a0.get()});
                                   _stack.push_back(_Enter{_args.d_a1.get()});
                                 },
                                 [&](const typename expr::Cond _args) -> void {
                                   _stack.push_back(_Call6{_args});
                                   _stack.push_back(_Enter{_args.d_a0.get()});
                                 }},
                             _self->v());
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
                         const typename expr::Cond _args = _f._s0;
                         unsigned int _cond0 = _result;
                         if (0u < _cond0) {
                           _stack.push_back(_Enter{_args.d_a1.get()});
                         } else {
                           _stack.push_back(_Enter{_args.d_a2.get()});
                         }
                       }},
            _frame);
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<expr>, T1> F1,
        MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2,
        MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F3,
        MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1,
               std::shared_ptr<expr>, T1>
            F4>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename expr::Succ &>().d_a0) _s0;
      };

      struct _Call2 {
        decltype(std::declval<const typename expr::Add &>().d_a0.get()) _s0;
        decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
      };

      struct _Call3 {
        T1 _s0;
        decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
      };

      struct _Call4 {
        decltype(std::declval<const typename expr::Mul &>().d_a0.get()) _s0;
        decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
      };

      struct _Call5 {
        T1 _s0;
        decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
      };

      struct _Call6 {
        const expr *_s0;
        const expr *_s1;
        decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
      };

      struct _Call7 {
        T1 _s0;
        const expr *_s1;
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

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4,
                                  _Call5, _Call6, _Call7, _Call8>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename expr::Succ _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          },
                          [&](const typename expr::Add _args) -> void {
                            _stack.push_back(_Call2{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename expr::Mul _args) -> void {
                            _stack.push_back(_Call4{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename expr::Cond _args) -> void {
                            _stack.push_back(
                                _Call6{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) { _result = f0(_f._s0, _result); },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call3 _f) {
                  _result = f1(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call4 _f) {
                  _stack.push_back(_Call5{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call5 _f) {
                  _result = f2(_f._s2, _result, _f._s1, _f._s0);
                },
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

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<expr>, T1> F1,
        MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2,
        MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F3,
        MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1,
               std::shared_ptr<expr>, T1>
            F4>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename expr::Succ &>().d_a0) _s0;
      };

      struct _Call2 {
        decltype(std::declval<const typename expr::Add &>().d_a0.get()) _s0;
        decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
      };

      struct _Call3 {
        T1 _s0;
        decltype(std::declval<const typename expr::Add &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Add &>().d_a0) _s2;
      };

      struct _Call4 {
        decltype(std::declval<const typename expr::Mul &>().d_a0.get()) _s0;
        decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
      };

      struct _Call5 {
        T1 _s0;
        decltype(std::declval<const typename expr::Mul &>().d_a1) _s1;
        decltype(std::declval<const typename expr::Mul &>().d_a0) _s2;
      };

      struct _Call6 {
        const expr *_s0;
        const expr *_s1;
        decltype(std::declval<const typename expr::Cond &>().d_a2) _s2;
        decltype(std::declval<const typename expr::Cond &>().d_a1) _s3;
        decltype(std::declval<const typename expr::Cond &>().d_a0) _s4;
      };

      struct _Call7 {
        T1 _s0;
        const expr *_s1;
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

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4,
                                  _Call5, _Call6, _Call7, _Call8>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename expr::Val _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename expr::Succ _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          },
                          [&](const typename expr::Add _args) -> void {
                            _stack.push_back(_Call2{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename expr::Mul _args) -> void {
                            _stack.push_back(_Call4{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename expr::Cond _args) -> void {
                            _stack.push_back(
                                _Call6{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) { _result = f0(_f._s0, _result); },
                [&](_Call2 _f) {
                  _stack.push_back(_Call3{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call3 _f) {
                  _result = f1(_f._s2, _result, _f._s1, _f._s0);
                },
                [&](_Call4 _f) {
                  _stack.push_back(_Call5{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call5 _f) {
                  _result = f2(_f._s2, _result, _f._s1, _f._s0);
                },
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
  };

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

  public:
    // CREATORS
    explicit simple_expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(Plus _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(IfPos _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<simple_expr> lit(unsigned int a0) {
      return std::make_shared<simple_expr>(Lit{std::move(a0)});
    }

    static std::shared_ptr<simple_expr>
    plus(const std::shared_ptr<simple_expr> &a0,
         const std::shared_ptr<simple_expr> &a1) {
      return std::make_shared<simple_expr>(Plus{a0, a1});
    }

    static std::shared_ptr<simple_expr>
    plus(std::shared_ptr<simple_expr> &&a0, std::shared_ptr<simple_expr> &&a1) {
      return std::make_shared<simple_expr>(Plus{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<simple_expr>
    ifpos(const std::shared_ptr<simple_expr> &a0,
          const std::shared_ptr<simple_expr> &a1,
          const std::shared_ptr<simple_expr> &a2) {
      return std::make_shared<simple_expr>(IfPos{a0, a1, a2});
    }

    static std::shared_ptr<simple_expr>
    ifpos(std::shared_ptr<simple_expr> &&a0, std::shared_ptr<simple_expr> &&a1,
          std::shared_ptr<simple_expr> &&a2) {
      return std::make_shared<simple_expr>(
          IfPos{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<simple_expr> lit_uptr(unsigned int a0) {
      return std::make_unique<simple_expr>(Lit{std::move(a0)});
    }

    static std::unique_ptr<simple_expr>
    plus_uptr(const std::shared_ptr<simple_expr> &a0,
              const std::shared_ptr<simple_expr> &a1) {
      return std::make_unique<simple_expr>(Plus{a0, a1});
    }

    static std::unique_ptr<simple_expr>
    plus_uptr(std::shared_ptr<simple_expr> &&a0,
              std::shared_ptr<simple_expr> &&a1) {
      return std::make_unique<simple_expr>(Plus{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<simple_expr>
    ifpos_uptr(const std::shared_ptr<simple_expr> &a0,
               const std::shared_ptr<simple_expr> &a1,
               const std::shared_ptr<simple_expr> &a2) {
      return std::make_unique<simple_expr>(IfPos{a0, a1, a2});
    }

    static std::unique_ptr<simple_expr>
    ifpos_uptr(std::shared_ptr<simple_expr> &&a0,
               std::shared_ptr<simple_expr> &&a1,
               std::shared_ptr<simple_expr> &&a2) {
      return std::make_unique<simple_expr>(
          IfPos{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// depth_simple e computes depth of simple expression tree.
    __attribute__((pure)) unsigned int depth_simple() const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_expr::Plus &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
      };

      struct _Call4 {
        unsigned int _s0;
        const simple_expr *_s1;
      };

      struct _Call5 {
        unsigned int _s0;
        unsigned int _s1;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const simple_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename simple_expr::Lit _args) -> void {
                            _result = 0u;
                          },
                          [&](const typename simple_expr::Plus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename simple_expr::IfPos _args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
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

    /// eval_simple e evaluates simple expression with positive test.
    __attribute__((pure)) unsigned int eval_simple() const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_expr::Plus &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        const typename simple_expr::IfPos _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const simple_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename simple_expr::Lit _args) -> void {
                            _result = _args.d_a0;
                          },
                          [&](const typename simple_expr::Plus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename simple_expr::IfPos _args) -> void {
                            _stack.push_back(_Call3{_args});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result + _f._s0); },
                [&](_Call3 _f) {
                  const typename simple_expr::IfPos _args = _f._s0;
                  unsigned int _cond0 = _result;
                  if (0u < _cond0) {
                    _stack.push_back(_Enter{_args.d_a1.get()});
                  } else {
                    _stack.push_back(_Enter{_args.d_a2.get()});
                  }
                }},
            _frame);
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<simple_expr>, T1,
                     std::shared_ptr<simple_expr>, T1>
                  F1,
              MapsTo<T1, std::shared_ptr<simple_expr>, T1,
                     std::shared_ptr<simple_expr>, T1,
                     std::shared_ptr<simple_expr>, T1>
                  F2>
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_expr::Plus &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
      };

      struct _Call3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
        decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
        decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
        decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
      };

      struct _Call4 {
        T1 _s0;
        const simple_expr *_s1;
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

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const simple_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename simple_expr::Lit _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename simple_expr::Plus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename simple_expr::IfPos _args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
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

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, std::shared_ptr<simple_expr>, T1,
                     std::shared_ptr<simple_expr>, T1>
                  F1,
              MapsTo<T1, std::shared_ptr<simple_expr>, T1,
                     std::shared_ptr<simple_expr>, T1,
                     std::shared_ptr<simple_expr>, T1>
                  F2>
    T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename simple_expr::Plus &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a1) _s1;
        decltype(std::declval<const typename simple_expr::Plus &>().d_a0) _s2;
      };

      struct _Call3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
        decltype(std::declval<const typename simple_expr::IfPos &>().d_a2) _s2;
        decltype(std::declval<const typename simple_expr::IfPos &>().d_a1) _s3;
        decltype(std::declval<const typename simple_expr::IfPos &>().d_a0) _s4;
      };

      struct _Call4 {
        T1 _s0;
        const simple_expr *_s1;
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

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const simple_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename simple_expr::Lit _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename simple_expr::Plus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename simple_expr::IfPos _args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
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
  };

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

  public:
    // CREATORS
    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<shape> circle(unsigned int a0) {
      return std::make_shared<shape>(Circle{std::move(a0)});
    }

    static std::shared_ptr<shape> square(unsigned int a0) {
      return std::make_shared<shape>(Square{std::move(a0)});
    }

    static std::shared_ptr<shape> triangle(unsigned int a0) {
      return std::make_shared<shape>(Triangle{std::move(a0)});
    }

    static std::unique_ptr<shape> circle_uptr(unsigned int a0) {
      return std::make_unique<shape>(Circle{std::move(a0)});
    }

    static std::unique_ptr<shape> square_uptr(unsigned int a0) {
      return std::make_unique<shape>(Square{std::move(a0)});
    }

    static std::unique_ptr<shape> triangle_uptr(unsigned int a0) {
      return std::make_unique<shape>(Triangle{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
    T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
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
          this->v());
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
    T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
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
          this->v());
    }
  };

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

  public:
    // CREATORS
    explicit cond_expr(CLit _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CPlus _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CCond _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<cond_expr> clit(unsigned int a0) {
      return std::make_shared<cond_expr>(CLit{std::move(a0)});
    }

    static std::shared_ptr<cond_expr>
    cplus(const std::shared_ptr<cond_expr> &a0,
          const std::shared_ptr<cond_expr> &a1) {
      return std::make_shared<cond_expr>(CPlus{a0, a1});
    }

    static std::shared_ptr<cond_expr> cplus(std::shared_ptr<cond_expr> &&a0,
                                            std::shared_ptr<cond_expr> &&a1) {
      return std::make_shared<cond_expr>(CPlus{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<cond_expr>
    ccond(const std::shared_ptr<cond_expr> &a0,
          const std::shared_ptr<cond_expr> &a1,
          const std::shared_ptr<cond_expr> &a2) {
      return std::make_shared<cond_expr>(CCond{a0, a1, a2});
    }

    static std::shared_ptr<cond_expr> ccond(std::shared_ptr<cond_expr> &&a0,
                                            std::shared_ptr<cond_expr> &&a1,
                                            std::shared_ptr<cond_expr> &&a2) {
      return std::make_shared<cond_expr>(
          CCond{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::unique_ptr<cond_expr> clit_uptr(unsigned int a0) {
      return std::make_unique<cond_expr>(CLit{std::move(a0)});
    }

    static std::unique_ptr<cond_expr>
    cplus_uptr(const std::shared_ptr<cond_expr> &a0,
               const std::shared_ptr<cond_expr> &a1) {
      return std::make_unique<cond_expr>(CPlus{a0, a1});
    }

    static std::unique_ptr<cond_expr>
    cplus_uptr(std::shared_ptr<cond_expr> &&a0,
               std::shared_ptr<cond_expr> &&a1) {
      return std::make_unique<cond_expr>(CPlus{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<cond_expr>
    ccond_uptr(const std::shared_ptr<cond_expr> &a0,
               const std::shared_ptr<cond_expr> &a1,
               const std::shared_ptr<cond_expr> &a2) {
      return std::make_unique<cond_expr>(CCond{a0, a1, a2});
    }

    static std::unique_ptr<cond_expr>
    ccond_uptr(std::shared_ptr<cond_expr> &&a0, std::shared_ptr<cond_expr> &&a1,
               std::shared_ptr<cond_expr> &&a2) {
      return std::make_unique<cond_expr>(
          CCond{std::move(a0), std::move(a1), std::move(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// depth_cond e computes depth of conditional expression tree.
    __attribute__((pure)) unsigned int depth_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::CPlus &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
      };

      struct _Call4 {
        unsigned int _s0;
        const cond_expr *_s1;
      };

      struct _Call5 {
        unsigned int _s0;
        unsigned int _s1;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::CLit _args) -> void {
                            _result = 0u;
                          },
                          [&](const typename cond_expr::CPlus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::CCond _args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
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

    /// eval_cond e evaluates conditional expression.
    __attribute__((pure)) unsigned int eval_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::CPlus &>()
                     .d_a0.get()) _s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        const typename cond_expr::CCond _s0;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::CLit _args) -> void {
                            _result = _args.d_a0;
                          },
                          [&](const typename cond_expr::CPlus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get()});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::CCond _args) -> void {
                            _stack.push_back(_Call3{_args});
                            _stack.push_back(_Enter{_args.d_a0.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) { _result = (_result + _f._s0); },
                [&](_Call3 _f) {
                  const typename cond_expr::CCond _args = _f._s0;
                  unsigned int _cond0 = _result;
                  if (0u < _cond0) {
                    _stack.push_back(_Enter{_args.d_a1.get()});
                  } else {
                    _stack.push_back(_Enter{_args.d_a2.get()});
                  }
                }},
            _frame);
      }
      return _result;
    }

    template <
        typename T1, MapsTo<T1, unsigned int> F0,
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1>
            F1,
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1, std::shared_ptr<cond_expr>, T1>
            F2>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::CPlus &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
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

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::CLit _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename cond_expr::CPlus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::CCond _args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
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
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1>
            F1,
        MapsTo<T1, std::shared_ptr<cond_expr>, T1, std::shared_ptr<cond_expr>,
               T1, std::shared_ptr<cond_expr>, T1>
            F2>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        decltype(std::declval<const typename cond_expr::CPlus &>()
                     .d_a0.get()) _s0;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
      };

      struct _Call2 {
        T1 _s0;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a1) _s1;
        decltype(std::declval<const typename cond_expr::CPlus &>().d_a0) _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        decltype(std::declval<const typename cond_expr::CCond &>().d_a2) _s2;
        decltype(std::declval<const typename cond_expr::CCond &>().d_a1) _s3;
        decltype(std::declval<const typename cond_expr::CCond &>().d_a0) _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
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

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.push_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        std::visit(
            Overloaded{
                [&](_Enter _f) {
                  const cond_expr *_self = _f._self;
                  std::visit(
                      Overloaded{
                          [&](const typename cond_expr::CLit _args) -> void {
                            _result = f(_args.d_a0);
                          },
                          [&](const typename cond_expr::CPlus _args) -> void {
                            _stack.push_back(_Call1{_args.d_a0.get(),
                                                    _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a1.get()});
                          },
                          [&](const typename cond_expr::CCond _args) -> void {
                            _stack.push_back(
                                _Call3{_args.d_a1.get(), _args.d_a0.get(),
                                       _args.d_a2, _args.d_a1, _args.d_a0});
                            _stack.push_back(_Enter{_args.d_a2.get()});
                          }},
                      _self->v());
                },
                [&](_Call1 _f) {
                  _stack.push_back(_Call2{_result, _f._s1, _f._s2});
                  _stack.push_back(_Enter{_f._s0});
                },
                [&](_Call2 _f) {
                  _result = f0(_f._s2, _result, _f._s1, _f._s0);
                },
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
  };
};

#endif // INCLUDED_LOOPIFY_EXPR
