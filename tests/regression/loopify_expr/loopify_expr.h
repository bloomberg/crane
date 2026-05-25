#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

#include <algorithm>
#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LoopifyExpr {
  /// Simple expression ADT with multiple recursive constructors.
  struct expr {
    // TYPES
    struct Val {
      uint64_t a0;
    };

    struct Succ {
      std::shared_ptr<expr> a0;
    };

    struct Add {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct Mul {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct Cond {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
    };

    using variant_t = std::variant<Val, Succ, Add, Mul, Cond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Val _v) : v_(std::move(_v)) {}

    explicit expr(Succ _v) : v_(std::move(_v)) {}

    explicit expr(Add _v) : v_(std::move(_v)) {}

    explicit expr(Mul _v) : v_(std::move(_v)) {}

    explicit expr(Cond _v) : v_(std::move(_v)) {}

    static expr val(uint64_t a0) { return expr(Val{a0}); }

    static expr succ(expr a0) {
      return expr(Succ{std::make_shared<expr>(std::move(a0))});
    }

    static expr add(expr a0, expr a1) {
      return expr(Add{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    static expr mul(expr a0, expr a1) {
      return expr(Mul{std::make_shared<expr>(std::move(a0)),
                      std::make_shared<expr>(std::move(a1))});
    }

    static expr cond(expr a0, expr a1, expr a2) {
      return expr(Cond{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1)),
                       std::make_shared<expr>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// simplify e performs algebraic simplification:
    /// Add(x, Val 0) = x, Add(Val 0, x) = x,
    /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
    expr simplify() const {
      if (std::holds_alternative<typename expr::Val>(this->v())) {
        const auto &[a0] = std::get<typename expr::Val>(this->v());
        return expr::val(a0);
      } else if (std::holds_alternative<typename expr::Succ>(this->v())) {
        const auto &[a0] = std::get<typename expr::Succ>(this->v());
        return expr::succ(a0->simplify());
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        auto &&_sv0 = a0->simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Val>(_sv0.v());
          if (a00 <= 0) {
            return a1->simplify();
          } else {
            uint64_t n0 = a00 - 1;
            expr s1 = expr::val((n0 + 1));
            auto &&_sv1 = a1->simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
              if (a01 <= 0) {
                return s1;
              } else {
                uint64_t n2 = a01 - 1;
                return expr::add(std::move(s1), expr::val((n2 + 1)));
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
              return expr::add(std::move(s1), expr::succ(*a01));
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
              return expr::add(std::move(s1), expr::add(*a01, *a11));
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
              return expr::add(std::move(s1), expr::mul(*a01, *a11));
            } else {
              const auto &[a01, a11, a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*a00);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else {
          const auto &[a00, a10, a20] = std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*a00, *a10, *a20);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return s1;
            } else {
              uint64_t n0 = a01 - 1;
              return expr::add(std::move(s1), expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        }
      } else if (std::holds_alternative<typename expr::Mul>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        auto &&_sv0 = a0->simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Val>(_sv0.v());
          if (a00 <= 0) {
            return expr::val(UINT64_C(0));
          } else {
            uint64_t _x = a00 - 1;
            auto &&_sv1 = a1->simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
              if (a01 <= 0) {
                return expr::val(UINT64_C(0));
              } else {
                uint64_t n1 = a01 - 1;
                expr s2 = expr::val((n1 + 1));
                if (a00 == UINT64_C(1)) {
                  return s2;
                } else {
                  return expr::mul(expr::val(a00), std::move(s2));
                }
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
              expr s2 = expr::succ(*a01);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
              expr s2 = expr::add(*a01, *a11);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
              expr s2 = expr::mul(*a01, *a11);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            } else {
              const auto &[a01, a11, a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              expr s2 = expr::cond(*a01, *a11, *a21);
              if (a00 == UINT64_C(1)) {
                return s2;
              } else {
                return expr::mul(expr::val(a00), std::move(s2));
              }
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*a00);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*a00, *a10);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        } else {
          const auto &[a00, a10, a20] = std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*a00, *a10, *a20);
          auto &&_sv1 = a1->simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Val>(_sv1.v());
            if (a01 <= 0) {
              return expr::val(UINT64_C(0));
            } else {
              uint64_t _x = a01 - 1;
              if (a01 == UINT64_C(1)) {
                return s1;
              } else {
                return expr::mul(std::move(s1), expr::val(a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(std::move(s1), expr::succ(*a01));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(std::move(s1), expr::add(*a01, *a11));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[a01, a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(std::move(s1), expr::mul(*a01, *a11));
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(std::move(s1), expr::cond(*a01, *a11, *a21));
          }
        }
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(this->v());
        return expr::cond(a0->simplify(), a1->simplify(), a2->simplify());
      }
    }

    /// size e counts total number of nodes.
    uint64_t size() const {
      if (std::holds_alternative<typename expr::Val>(this->v())) {
        return UINT64_C(1);
      } else if (std::holds_alternative<typename expr::Succ>(this->v())) {
        const auto &[a0] = std::get<typename expr::Succ>(this->v());
        return (a0->size() + 1);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return ((a0->size() + a1->size()) + 1);
      } else if (std::holds_alternative<typename expr::Mul>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return ((a0->size() + a1->size()) + 1);
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(this->v());
        return ((a0->size() + (a1->size() + a2->size())) + 1);
      }
    }

    /// count_vals e counts the number of Val nodes.
    uint64_t count_vals() const {
      if (std::holds_alternative<typename expr::Val>(this->v())) {
        return UINT64_C(1);
      } else if (std::holds_alternative<typename expr::Succ>(this->v())) {
        const auto &[a0] = std::get<typename expr::Succ>(this->v());
        return a0->count_vals();
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return (a0->count_vals() + a1->count_vals());
      } else if (std::holds_alternative<typename expr::Mul>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return (a0->count_vals() + a1->count_vals());
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(this->v());
        return (a0->count_vals() + (a1->count_vals() + a2->count_vals()));
      }
    }

    /// depth e computes expression depth.
    uint64_t depth() const {
      if (std::holds_alternative<typename expr::Val>(this->v())) {
        return UINT64_C(0);
      } else if (std::holds_alternative<typename expr::Succ>(this->v())) {
        const auto &[a0] = std::get<typename expr::Succ>(this->v());
        return (a0->depth() + 1);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return (std::max(a0->depth(), a1->depth()) + 1);
      } else if (std::holds_alternative<typename expr::Mul>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return (std::max(a0->depth(), a1->depth()) + 1);
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(this->v());
        return (std::max(a0->depth(), std::max(a1->depth(), a2->depth())) + 1);
      }
    }

    /// eval e evaluates an expression. Multi-constructor recursion.
    uint64_t eval() const {
      if (std::holds_alternative<typename expr::Val>(this->v())) {
        const auto &[a0] = std::get<typename expr::Val>(this->v());
        return a0;
      } else if (std::holds_alternative<typename expr::Succ>(this->v())) {
        const auto &[a0] = std::get<typename expr::Succ>(this->v());
        return (a0->eval() + 1);
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return (a0->eval() + a1->eval());
      } else if (std::holds_alternative<typename expr::Mul>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return (a0->eval() * a1->eval());
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(this->v());
        if (UINT64_C(0) < a0->eval()) {
          return a1->eval();
        } else {
          return a2->eval();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, expr &, T1 &, expr &, T1 &,
                                     expr &, T1 &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      if (std::holds_alternative<typename expr::Val>(this->v())) {
        const auto &[a0] = std::get<typename expr::Val>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Succ>(this->v())) {
        const auto &[a0] = std::get<typename expr::Succ>(this->v());
        return f0(*a0, a0->template expr_rec<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return f1(*a0, a0->template expr_rec<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template expr_rec<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename expr::Mul>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return f2(*a0, a0->template expr_rec<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template expr_rec<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(this->v());
        return f3(*a0, a0->template expr_rec<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template expr_rec<T1>(f, f0, f1, f2, f3), *a2,
                  a2->template expr_rec<T1>(f, f0, f1, f2, f3));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3,
              typename F4>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, expr &, T1 &, expr &, T1 &,
                                     expr &, T1 &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      if (std::holds_alternative<typename expr::Val>(this->v())) {
        const auto &[a0] = std::get<typename expr::Val>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename expr::Succ>(this->v())) {
        const auto &[a0] = std::get<typename expr::Succ>(this->v());
        return f0(*a0, a0->template expr_rect<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Add>(this->v());
        return f1(*a0, a0->template expr_rect<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template expr_rect<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename expr::Mul>(this->v())) {
        const auto &[a0, a1] = std::get<typename expr::Mul>(this->v());
        return f2(*a0, a0->template expr_rect<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template expr_rect<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[a0, a1, a2] = std::get<typename expr::Cond>(this->v());
        return f3(*a0, a0->template expr_rect<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template expr_rect<T1>(f, f0, f1, f2, f3), *a2,
                  a2->template expr_rect<T1>(f, f0, f1, f2, f3));
      }
    }
  };

  /// Alternative expression type for testing different evaluation strategy.
  struct simple_expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Plus {
      std::shared_ptr<simple_expr> a0;
      std::shared_ptr<simple_expr> a1;
    };

    struct IfPos {
      std::shared_ptr<simple_expr> a0;
      std::shared_ptr<simple_expr> a1;
      std::shared_ptr<simple_expr> a2;
    };

    using variant_t = std::variant<Lit, Plus, IfPos>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    simple_expr() {}

    explicit simple_expr(Lit _v) : v_(std::move(_v)) {}

    explicit simple_expr(Plus _v) : v_(std::move(_v)) {}

    explicit simple_expr(IfPos _v) : v_(std::move(_v)) {}

    static simple_expr lit(uint64_t a0) { return simple_expr(Lit{a0}); }

    static simple_expr plus(simple_expr a0, simple_expr a1) {
      return simple_expr(Plus{std::make_shared<simple_expr>(std::move(a0)),
                              std::make_shared<simple_expr>(std::move(a1))});
    }

    static simple_expr ifpos(simple_expr a0, simple_expr a1, simple_expr a2) {
      return simple_expr(IfPos{std::make_shared<simple_expr>(std::move(a0)),
                               std::make_shared<simple_expr>(std::move(a1)),
                               std::make_shared<simple_expr>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// depth_simple e computes depth of simple expression tree.
    uint64_t depth_simple() const {
      if (std::holds_alternative<typename simple_expr::Lit>(this->v())) {
        return UINT64_C(0);
      } else if (std::holds_alternative<typename simple_expr::Plus>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename simple_expr::Plus>(this->v());
        return (std::max(a0->depth_simple(), a1->depth_simple()) + 1);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename simple_expr::IfPos>(this->v());
        return (std::max(a0->depth_simple(),
                         std::max(a1->depth_simple(), a2->depth_simple())) +
                1);
      }
    }

    /// eval_simple e evaluates simple expression with positive test.
    uint64_t eval_simple() const {
      if (std::holds_alternative<typename simple_expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename simple_expr::Lit>(this->v());
        return a0;
      } else if (std::holds_alternative<typename simple_expr::Plus>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename simple_expr::Plus>(this->v());
        return (a0->eval_simple() + a1->eval_simple());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename simple_expr::IfPos>(this->v());
        if (UINT64_C(0) < a0->eval_simple()) {
          return a1->eval_simple();
        } else {
          return a2->eval_simple();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &, simple_expr &, T1 &>
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename simple_expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename simple_expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename simple_expr::Plus>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename simple_expr::Plus>(this->v());
        return f0(*a0, a0->template simple_expr_rec<T1>(f, f0, f1), *a1,
                  a1->template simple_expr_rec<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename simple_expr::IfPos>(this->v());
        return f1(*a0, a0->template simple_expr_rec<T1>(f, f0, f1), *a1,
                  a1->template simple_expr_rec<T1>(f, f0, f1), *a2,
                  a2->template simple_expr_rec<T1>(f, f0, f1));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, simple_expr &, T1 &,
                                     simple_expr &, T1 &, simple_expr &, T1 &>
    T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename simple_expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename simple_expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename simple_expr::Plus>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename simple_expr::Plus>(this->v());
        return f0(*a0, a0->template simple_expr_rect<T1>(f, f0, f1), *a1,
                  a1->template simple_expr_rect<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename simple_expr::IfPos>(this->v());
        return f1(*a0, a0->template simple_expr_rect<T1>(f, f0, f1), *a1,
                  a1->template simple_expr_rect<T1>(f, f0, f1), *a2,
                  a2->template simple_expr_rect<T1>(f, f0, f1));
      }
    }
  };

  /// Shape type demonstrating or-pattern matching.
  struct shape {
    // TYPES
    struct Circle {
      uint64_t a0;
    };

    struct Square {
      uint64_t a0;
    };

    struct Triangle {
      uint64_t a0;
    };

    using variant_t = std::variant<Circle, Square, Triangle>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    shape() {}

    explicit shape(Circle _v) : v_(std::move(_v)) {}

    explicit shape(Square _v) : v_(std::move(_v)) {}

    explicit shape(Triangle _v) : v_(std::move(_v)) {}

    static shape circle(uint64_t a0) { return shape(Circle{a0}); }

    static shape square(uint64_t a0) { return shape(Square{a0}); }

    static shape triangle(uint64_t a0) { return shape(Triangle{a0}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0] = std::get<typename shape::Circle>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename shape::Square>(this->v())) {
        const auto &[a0] = std::get<typename shape::Square>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename shape::Triangle>(this->v());
        return f1(a0);
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F2 &, uint64_t &>
    T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename shape::Circle>(this->v())) {
        const auto &[a0] = std::get<typename shape::Circle>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename shape::Square>(this->v())) {
        const auto &[a0] = std::get<typename shape::Square>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename shape::Triangle>(this->v());
        return f1(a0);
      }
    }
  };

  /// sum_shapes l sums values from shapes using unified pattern.
  /// Tests or-pattern style matching in Coq.
  static uint64_t sum_shapes(const List<shape> &l);
  /// count_by_shape l counts shapes: (circles, squares, triangles).
  static std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
  count_by_shape(const List<shape> &l);

  /// Alternative expression type with conditionals for testing different
  /// evaluation patterns.
  struct cond_expr {
    // TYPES
    struct CLit {
      uint64_t a0;
    };

    struct CPlus {
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
    };

    struct CCond {
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
      std::shared_ptr<cond_expr> a2;
    };

    using variant_t = std::variant<CLit, CPlus, CCond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(CLit _v) : v_(std::move(_v)) {}

    explicit cond_expr(CPlus _v) : v_(std::move(_v)) {}

    explicit cond_expr(CCond _v) : v_(std::move(_v)) {}

    static cond_expr clit(uint64_t a0) { return cond_expr(CLit{a0}); }

    static cond_expr cplus(cond_expr a0, cond_expr a1) {
      return cond_expr(CPlus{std::make_shared<cond_expr>(std::move(a0)),
                             std::make_shared<cond_expr>(std::move(a1))});
    }

    static cond_expr ccond(cond_expr a0, cond_expr a1, cond_expr a2) {
      return cond_expr(CCond{std::make_shared<cond_expr>(std::move(a0)),
                             std::make_shared<cond_expr>(std::move(a1)),
                             std::make_shared<cond_expr>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// depth_cond e computes depth of conditional expression tree.
    uint64_t depth_cond() const {
      if (std::holds_alternative<typename cond_expr::CLit>(this->v())) {
        return UINT64_C(0);
      } else if (std::holds_alternative<typename cond_expr::CPlus>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(this->v());
        return (std::max(a0->depth_cond(), a1->depth_cond()) + 1);
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::CCond>(this->v());
        return (std::max(a0->depth_cond(),
                         std::max(a1->depth_cond(), a2->depth_cond())) +
                1);
      }
    }

    /// eval_cond e evaluates conditional expression.
    uint64_t eval_cond() const {
      if (std::holds_alternative<typename cond_expr::CLit>(this->v())) {
        const auto &[a0] = std::get<typename cond_expr::CLit>(this->v());
        return a0;
      } else if (std::holds_alternative<typename cond_expr::CPlus>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(this->v());
        return (a0->eval_cond() + a1->eval_cond());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::CCond>(this->v());
        if (UINT64_C(0) < a0->eval_cond()) {
          return a1->eval_cond();
        } else {
          return a2->eval_cond();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename cond_expr::CLit>(this->v())) {
        const auto &[a0] = std::get<typename cond_expr::CLit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename cond_expr::CPlus>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(this->v());
        return f0(*a0, a0->template cond_expr_rec<T1>(f, f0, f1), *a1,
                  a1->template cond_expr_rec<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::CCond>(this->v());
        return f1(*a0, a0->template cond_expr_rec<T1>(f, f0, f1), *a1,
                  a1->template cond_expr_rec<T1>(f, f0, f1), *a2,
                  a2->template cond_expr_rec<T1>(f, f0, f1));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, cond_expr &, T1 &, cond_expr &,
                                     T1 &, cond_expr &, T1 &>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename cond_expr::CLit>(this->v())) {
        const auto &[a0] = std::get<typename cond_expr::CLit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename cond_expr::CPlus>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::CPlus>(this->v());
        return f0(*a0, a0->template cond_expr_rect<T1>(f, f0, f1), *a1,
                  a1->template cond_expr_rect<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::CCond>(this->v());
        return f1(*a0, a0->template cond_expr_rect<T1>(f, f0, f1), *a1,
                  a1->template cond_expr_rect<T1>(f, f0, f1), *a2,
                  a2->template cond_expr_rect<T1>(f, f0, f1));
      }
    }
  };
};

#endif // INCLUDED_LOOPIFY_EXPR
