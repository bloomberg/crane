#ifndef INCLUDED_LOOPIFY_EXPR
#define INCLUDED_LOOPIFY_EXPR

#include <algorithm>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
          d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

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
      std::unique_ptr<expr> d_a0;
    };

    struct Add {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct Mul {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct Cond {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
      std::unique_ptr<expr> d_a2;
    };

    using variant_t = std::variant<Val, Succ, Add, Mul, Cond>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Val _v) : d_v_(std::move(_v)) {}

    explicit expr(Succ _v) : d_v_(std::move(_v)) {}

    explicit expr(Add _v) : d_v_(std::move(_v)) {}

    explicit expr(Mul _v) : d_v_(std::move(_v)) {}

    explicit expr(Cond _v) : d_v_(std::move(_v)) {}

    expr(const expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    expr(expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) expr &operator=(const expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) expr &operator=(expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Val>(_sv.v())) {
        const auto &[d_a0] = std::get<Val>(_sv.v());
        return expr(Val{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else if (std::holds_alternative<Succ>(_sv.v())) {
        const auto &[d_a0] = std::get<Succ>(_sv.v());
        return expr(
            Succ{d_a0 ? std::make_unique<LoopifyExpr::expr>(d_a0->clone())
                      : nullptr});
      } else if (std::holds_alternative<Add>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Add>(_sv.v());
        return expr(Add{
            d_a0 ? std::make_unique<LoopifyExpr::expr>(d_a0->clone()) : nullptr,
            d_a1 ? std::make_unique<LoopifyExpr::expr>(d_a1->clone())
                 : nullptr});
      } else if (std::holds_alternative<Mul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Mul>(_sv.v());
        return expr(Mul{
            d_a0 ? std::make_unique<LoopifyExpr::expr>(d_a0->clone()) : nullptr,
            d_a1 ? std::make_unique<LoopifyExpr::expr>(d_a1->clone())
                 : nullptr});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<Cond>(_sv.v());
        return expr(Cond{
            d_a0 ? std::make_unique<LoopifyExpr::expr>(d_a0->clone()) : nullptr,
            d_a1 ? std::make_unique<LoopifyExpr::expr>(d_a1->clone()) : nullptr,
            d_a2 ? std::make_unique<LoopifyExpr::expr>(d_a2->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static expr val(unsigned int a0) {
      return expr(Val{std::move(a0)});
    }

    __attribute__((pure)) static expr succ(const expr &a0) {
      return expr(Succ{std::make_unique<expr>(a0)});
    }

    __attribute__((pure)) static expr add(const expr &a0, const expr &a1) {
      return expr(Add{std::make_unique<expr>(a0), std::make_unique<expr>(a1)});
    }

    __attribute__((pure)) static expr mul(const expr &a0, const expr &a1) {
      return expr(Mul{std::make_unique<expr>(a0), std::make_unique<expr>(a1)});
    }

    __attribute__((pure)) static expr cond(const expr &a0, const expr &a1,
                                           const expr &a2) {
      return expr(Cond{std::make_unique<expr>(a0), std::make_unique<expr>(a1),
                       std::make_unique<expr>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) expr *operator->() { return this; }

    __attribute__((pure)) const expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// simplify e performs algebraic simplification:
    /// Add(x, Val 0) = x, Add(Val 0, x) = x,
    /// Mul(x, Val 1) = x, Mul(Val 1, x) = x,
    /// Mul(_, Val 0) = Val 0, Mul(Val 0, _) = Val 0.
    __attribute__((pure)) expr simplify() const {
      const expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename expr::Val>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
        return expr::val(d_a0);
      } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
        return expr::succ((*(d_a0)).simplify());
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
        auto &&_sv0 = (*(d_a0)).simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Val>(_sv0.v());
          if (d_a00 <= 0) {
            return (*(d_a1)).simplify();
          } else {
            unsigned int n0 = d_a00 - 1;
            expr s1 = expr::val((n0 + 1));
            auto &&_sv1 = (*(d_a1)).simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
              if (d_a01 <= 0) {
                return s1;
              } else {
                unsigned int n2 = d_a01 - 1;
                return expr::add(s1, expr::val((n2 + 1)));
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
              return expr::add(s1, expr::succ(*(d_a01)));
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Add>(_sv1.v());
              return expr::add(s1, expr::add(*(d_a01), *(d_a11)));
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Mul>(_sv1.v());
              return expr::add(s1, expr::mul(*(d_a01), *(d_a11)));
            } else {
              const auto &[d_a01, d_a11, d_a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              return expr::add(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*(d_a00));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(s1, expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(s1, expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(s1, expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*(d_a00), *(d_a10), *(d_a20));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return s1;
            } else {
              unsigned int n0 = d_a01 - 1;
              return expr::add(s1, expr::val((n0 + 1)));
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::add(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::add(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::add(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::add(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        }
      } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
        auto &&_sv0 = (*(d_a0)).simplify();
        if (std::holds_alternative<typename expr::Val>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Val>(_sv0.v());
          if (d_a00 <= 0) {
            return expr::val(0u);
          } else {
            unsigned int _x = d_a00 - 1;
            auto &&_sv1 = (*(d_a1)).simplify();
            if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
              if (d_a01 <= 0) {
                return expr::val(0u);
              } else {
                unsigned int n1 = d_a01 - 1;
                expr s2 = expr::val((n1 + 1));
                if (d_a00 == 1u) {
                  return s2;
                } else {
                  return expr::mul(expr::val(d_a00), s2);
                }
              }
            } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
              const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
              expr s2 = expr::succ(*(d_a01));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), s2);
              }
            } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Add>(_sv1.v());
              expr s2 = expr::add(*(d_a01), *(d_a11));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), s2);
              }
            } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
              const auto &[d_a01, d_a11] =
                  std::get<typename expr::Mul>(_sv1.v());
              expr s2 = expr::mul(*(d_a01), *(d_a11));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), s2);
              }
            } else {
              const auto &[d_a01, d_a11, d_a21] =
                  std::get<typename expr::Cond>(_sv1.v());
              expr s2 = expr::cond(*(d_a01), *(d_a11), *(d_a21));
              if (d_a00 == 1u) {
                return s2;
              } else {
                return expr::mul(expr::val(d_a00), s2);
              }
            }
          }
        } else if (std::holds_alternative<typename expr::Succ>(_sv0.v())) {
          const auto &[d_a00] = std::get<typename expr::Succ>(_sv0.v());
          expr s1 = expr::succ(*(d_a00));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(s1, expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Add>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Add>(_sv0.v());
          expr s1 = expr::add(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(s1, expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else if (std::holds_alternative<typename expr::Mul>(_sv0.v())) {
          const auto &[d_a00, d_a10] = std::get<typename expr::Mul>(_sv0.v());
          expr s1 = expr::mul(*(d_a00), *(d_a10));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(s1, expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        } else {
          const auto &[d_a00, d_a10, d_a20] =
              std::get<typename expr::Cond>(_sv0.v());
          expr s1 = expr::cond(*(d_a00), *(d_a10), *(d_a20));
          auto &&_sv1 = (*(d_a1)).simplify();
          if (std::holds_alternative<typename expr::Val>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Val>(_sv1.v());
            if (d_a01 <= 0) {
              return expr::val(0u);
            } else {
              unsigned int _x = d_a01 - 1;
              if (d_a01 == 1u) {
                return s1;
              } else {
                return expr::mul(s1, expr::val(d_a01));
              }
            }
          } else if (std::holds_alternative<typename expr::Succ>(_sv1.v())) {
            const auto &[d_a01] = std::get<typename expr::Succ>(_sv1.v());
            return expr::mul(s1, expr::succ(*(d_a01)));
          } else if (std::holds_alternative<typename expr::Add>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Add>(_sv1.v());
            return expr::mul(s1, expr::add(*(d_a01), *(d_a11)));
          } else if (std::holds_alternative<typename expr::Mul>(_sv1.v())) {
            const auto &[d_a01, d_a11] = std::get<typename expr::Mul>(_sv1.v());
            return expr::mul(s1, expr::mul(*(d_a01), *(d_a11)));
          } else {
            const auto &[d_a01, d_a11, d_a21] =
                std::get<typename expr::Cond>(_sv1.v());
            return expr::mul(s1, expr::cond(*(d_a01), *(d_a11), *(d_a21)));
          }
        }
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::Cond>(_sv.v());
        return expr::cond((*(d_a0)).simplify(), (*(d_a1)).simplify(),
                          (*(d_a2)).simplify());
      }
    }

    /// size e counts total number of nodes.
    __attribute__((pure)) unsigned int size() const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {};

      struct _Call2 {
        expr *_s0;
      };

      struct _Call3 {
        unsigned int _s0;
      };

      struct _Call4 {
        expr *_s0;
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
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = 1u;
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Call1{});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Call4{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Call6{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = (_result + 1);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = ((_result + _f._s0) + 1);
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = ((_result + _f._s0) + 1);
        } else if (std::holds_alternative<_Call6>(_frame)) {
          auto _f = std::move(std::get<_Call6>(_frame));
          _stack.emplace_back(_Call7{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call7>(_frame)) {
          auto _f = std::move(std::get<_Call7>(_frame));
          _stack.emplace_back(_Call8{_f._s0, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call8>(_frame));
          _result = ((_result + (_f._s1 + _f._s0)) + 1);
        }
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
        expr *_s0;
      };

      struct _Call2 {
        unsigned int _s0;
      };

      struct _Call3 {
        expr *_s0;
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
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = 1u;
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Call3{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Call5{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (_result + _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _result = (_result + _f._s0);
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _stack.emplace_back(_Call6{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call6>(_frame)) {
          auto _f = std::move(std::get<_Call6>(_frame));
          _stack.emplace_back(_Call7{_f._s0, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call7>(_frame));
          _result = (_result + (_f._s1 + _f._s0));
        }
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
        expr *_s0;
      };

      struct _Call3 {
        unsigned int _s0;
      };

      struct _Call4 {
        expr *_s0;
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
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Call1{});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Call4{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(_Call6{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = (_result + 1);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = (std::max(_result, _f._s0) + 1);
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = (std::max(_result, _f._s0) + 1);
        } else if (std::holds_alternative<_Call6>(_frame)) {
          auto _f = std::move(std::get<_Call6>(_frame));
          _stack.emplace_back(_Call7{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call7>(_frame)) {
          auto _f = std::move(std::get<_Call7>(_frame));
          _stack.emplace_back(_Call8{_f._s0, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call8>(_frame));
          _result = (std::max(_result, std::max(_f._s1, _f._s0)) + 1);
        }
      }
      return _result;
    }

    /// eval e evaluates an expression. Multi-constructor recursion.
    __attribute__((pure)) unsigned int eval() const {
      const expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename expr::Val>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
        const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
        return ((*(d_a0)).eval() + 1);
      } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
        return ((*(d_a0)).eval() + (*(d_a1)).eval());
      } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
        return ((*(d_a0)).eval() * (*(d_a1)).eval());
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::Cond>(_sv.v());
        if (0u < (*(d_a0)).eval()) {
          return (*(d_a1)).eval();
        } else {
          return (*(d_a2)).eval();
        }
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, expr, T1> F1,
              MapsTo<T1, expr, T1, expr, T1> F2,
              MapsTo<T1, expr, T1, expr, T1> F3,
              MapsTo<T1, expr, T1, expr, T1, expr, T1> F4>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {
        expr _s0;
      };

      struct _Call2 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      struct _Call3 {
        T1 _s0;
        expr _s1;
        expr _s2;
      };

      struct _Call4 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      struct _Call5 {
        T1 _s0;
        expr _s1;
        expr _s2;
      };

      struct _Call6 {
        const expr *_s0;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      struct _Call7 {
        T1 _s0;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      struct _Call8 {
        T1 _s0;
        T1 _s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4,
                                  _Call5, _Call6, _Call7, _Call8>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Call1{*(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Call4{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _Call6{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = f0(_f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call6>(_frame)) {
          auto _f = std::move(std::get<_Call6>(_frame));
          _stack.emplace_back(_Call7{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call7>(_frame)) {
          auto _f = std::move(std::get<_Call7>(_frame));
          _stack.emplace_back(_Call8{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call8>(_frame));
          _result = f3(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0, MapsTo<T1, expr, T1> F1,
              MapsTo<T1, expr, T1, expr, T1> F2,
              MapsTo<T1, expr, T1, expr, T1> F3,
              MapsTo<T1, expr, T1, expr, T1, expr, T1> F4>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const expr *_self = this;

      struct _Enter {
        const expr *_self;
      };

      struct _Call1 {
        expr _s0;
      };

      struct _Call2 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      struct _Call3 {
        T1 _s0;
        expr _s1;
        expr _s2;
      };

      struct _Call4 {
        expr *_s0;
        expr _s1;
        expr _s2;
      };

      struct _Call5 {
        T1 _s0;
        expr _s1;
        expr _s2;
      };

      struct _Call6 {
        const expr *_s0;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      struct _Call7 {
        T1 _s0;
        const expr *_s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      struct _Call8 {
        T1 _s0;
        T1 _s1;
        expr _s2;
        expr _s3;
        expr _s4;
      };

      using _Frame = std::variant<_Enter, _Call1, _Call2, _Call3, _Call4,
                                  _Call5, _Call6, _Call7, _Call8>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename expr::Val>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Val>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename expr::Succ>(_sv.v())) {
            const auto &[d_a0] = std::get<typename expr::Succ>(_sv.v());
            _stack.emplace_back(_Call1{*(d_a0)});
            _stack.emplace_back(_Enter{d_a0.get()});
          } else if (std::holds_alternative<typename expr::Add>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Add>(_sv.v());
            _stack.emplace_back(_Call2{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else if (std::holds_alternative<typename expr::Mul>(_sv.v())) {
            const auto &[d_a0, d_a1] = std::get<typename expr::Mul>(_sv.v());
            _stack.emplace_back(_Call4{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename expr::Cond>(_sv.v());
            _stack.emplace_back(
                _Call6{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _result = f0(_f._s0, _result);
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _stack.emplace_back(_Call3{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _result = f1(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call5>(_frame)) {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f2(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call6>(_frame)) {
          auto _f = std::move(std::get<_Call6>(_frame));
          _stack.emplace_back(_Call7{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call7>(_frame)) {
          auto _f = std::move(std::get<_Call7>(_frame));
          _stack.emplace_back(_Call8{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call8>(_frame));
          _result = f3(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
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
      std::unique_ptr<simple_expr> d_a0;
      std::unique_ptr<simple_expr> d_a1;
    };

    struct IfPos {
      std::unique_ptr<simple_expr> d_a0;
      std::unique_ptr<simple_expr> d_a1;
      std::unique_ptr<simple_expr> d_a2;
    };

    using variant_t = std::variant<Lit, Plus, IfPos>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    simple_expr() {}

    explicit simple_expr(Lit _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(Plus _v) : d_v_(std::move(_v)) {}

    explicit simple_expr(IfPos _v) : d_v_(std::move(_v)) {}

    simple_expr(const simple_expr &_other)
        : d_v_(std::move(_other.clone().d_v_)) {}

    simple_expr(simple_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) simple_expr &operator=(const simple_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) simple_expr &operator=(simple_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) simple_expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<Lit>(_sv.v());
        return simple_expr(Lit{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else if (std::holds_alternative<Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Plus>(_sv.v());
        return simple_expr(Plus{
            d_a0 ? std::make_unique<LoopifyExpr::simple_expr>(d_a0->clone())
                 : nullptr,
            d_a1 ? std::make_unique<LoopifyExpr::simple_expr>(d_a1->clone())
                 : nullptr});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<IfPos>(_sv.v());
        return simple_expr(IfPos{
            d_a0 ? std::make_unique<LoopifyExpr::simple_expr>(d_a0->clone())
                 : nullptr,
            d_a1 ? std::make_unique<LoopifyExpr::simple_expr>(d_a1->clone())
                 : nullptr,
            d_a2 ? std::make_unique<LoopifyExpr::simple_expr>(d_a2->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static simple_expr lit(unsigned int a0) {
      return simple_expr(Lit{std::move(a0)});
    }

    __attribute__((pure)) static simple_expr plus(const simple_expr &a0,
                                                  const simple_expr &a1) {
      return simple_expr(Plus{std::make_unique<simple_expr>(a0),
                              std::make_unique<simple_expr>(a1)});
    }

    __attribute__((pure)) static simple_expr
    ifpos(const simple_expr &a0, const simple_expr &a1, const simple_expr &a2) {
      return simple_expr(IfPos{std::make_unique<simple_expr>(a0),
                               std::make_unique<simple_expr>(a1),
                               std::make_unique<simple_expr>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) simple_expr *operator->() { return this; }

    __attribute__((pure)) const simple_expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = simple_expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// depth_simple e computes depth of simple expression tree.
    __attribute__((pure)) unsigned int depth_simple() const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      struct _Call1 {
        simple_expr *_s0;
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
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(_Call3{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (std::max(_result, _f._s0) + 1);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = (std::max(_result, std::max(_f._s1, _f._s0)) + 1);
        }
      }
      return _result;
    }

    /// eval_simple e evaluates simple expression with positive test.
    __attribute__((pure)) unsigned int eval_simple() const {
      const simple_expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename simple_expr::Lit>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename simple_expr::Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] =
            std::get<typename simple_expr::Plus>(_sv.v());
        return ((*(d_a0)).eval_simple() + (*(d_a1)).eval_simple());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename simple_expr::IfPos>(_sv.v());
        if (0u < (*(d_a0)).eval_simple()) {
          return (*(d_a1)).eval_simple();
        } else {
          return (*(d_a2)).eval_simple();
        }
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, simple_expr, T1, simple_expr, T1> F1,
              MapsTo<T1, simple_expr, T1, simple_expr, T1, simple_expr, T1> F2>
    T1 simple_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      struct _Call1 {
        simple_expr *_s0;
        simple_expr _s1;
        simple_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        simple_expr _s1;
        simple_expr _s2;
      };

      struct _Call3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      struct _Call4 {
        T1 _s0;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, simple_expr, T1, simple_expr, T1> F1,
              MapsTo<T1, simple_expr, T1, simple_expr, T1, simple_expr, T1> F2>
    T1 simple_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const simple_expr *_self = this;

      struct _Enter {
        const simple_expr *_self;
      };

      struct _Call1 {
        simple_expr *_s0;
        simple_expr _s1;
        simple_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        simple_expr _s1;
        simple_expr _s2;
      };

      struct _Call3 {
        const simple_expr *_s0;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      struct _Call4 {
        T1 _s0;
        const simple_expr *_s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        simple_expr _s2;
        simple_expr _s3;
        simple_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename simple_expr::Lit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename simple_expr::Lit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename simple_expr::Plus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename simple_expr::Plus>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename simple_expr::IfPos>(_sv.v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
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
    shape() {}

    explicit shape(Circle _v) : d_v_(std::move(_v)) {}

    explicit shape(Square _v) : d_v_(std::move(_v)) {}

    explicit shape(Triangle _v) : d_v_(std::move(_v)) {}

    shape(const shape &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    shape(shape &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) shape &operator=(const shape &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) shape &operator=(shape &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) shape clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<Circle>(_sv.v());
        return shape(Circle{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else if (std::holds_alternative<Square>(_sv.v())) {
        const auto &[d_a0] = std::get<Square>(_sv.v());
        return shape(Square{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else {
        const auto &[d_a0] = std::get<Triangle>(_sv.v());
        return shape(Triangle{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      }
    }

    // CREATORS
    __attribute__((pure)) static shape circle(unsigned int a0) {
      return shape(Circle{std::move(a0)});
    }

    __attribute__((pure)) static shape square(unsigned int a0) {
      return shape(Square{std::move(a0)});
    }

    __attribute__((pure)) static shape triangle(unsigned int a0) {
      return shape(Triangle{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) shape *operator->() { return this; }

    __attribute__((pure)) const shape *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = shape(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
    T1 shape_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename shape::Square>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Square>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename shape::Triangle>(_sv.v());
        return f1(d_a0);
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, unsigned int> F1, MapsTo<T1, unsigned int> F2>
    T1 shape_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename shape::Circle>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Circle>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename shape::Square>(_sv.v())) {
        const auto &[d_a0] = std::get<typename shape::Square>(_sv.v());
        return f0(d_a0);
      } else {
        const auto &[d_a0] = std::get<typename shape::Triangle>(_sv.v());
        return f1(d_a0);
      }
    }
  };

  /// sum_shapes l sums values from shapes using unified pattern.
  /// Tests or-pattern style matching in Coq.
  __attribute__((pure)) static unsigned int sum_shapes(const List<shape> &l);
  /// count_by_shape l counts shapes: (circles, squares, triangles).
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  count_by_shape(const List<shape> &l);

  /// Alternative expression type with conditionals for testing different
  /// evaluation patterns.
  struct cond_expr {
    // TYPES
    struct CLit {
      unsigned int d_a0;
    };

    struct CPlus {
      std::unique_ptr<cond_expr> d_a0;
      std::unique_ptr<cond_expr> d_a1;
    };

    struct CCond {
      std::unique_ptr<cond_expr> d_a0;
      std::unique_ptr<cond_expr> d_a1;
      std::unique_ptr<cond_expr> d_a2;
    };

    using variant_t = std::variant<CLit, CPlus, CCond>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(CLit _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CPlus _v) : d_v_(std::move(_v)) {}

    explicit cond_expr(CCond _v) : d_v_(std::move(_v)) {}

    cond_expr(const cond_expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    cond_expr(cond_expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) cond_expr &operator=(const cond_expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) cond_expr &operator=(cond_expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) cond_expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<CLit>(_sv.v())) {
        const auto &[d_a0] = std::get<CLit>(_sv.v());
        return cond_expr(CLit{[](auto &&__v) -> unsigned int {
          if constexpr (
              requires { __v ? 0 : 0; } && requires { *__v; } &&
              requires { __v->clone(); } && requires { __v.get(); }) {
            using _E = std::remove_cvref_t<decltype(*__v)>;
            return __v ? std::make_unique<_E>(__v->clone()) : nullptr;
          } else if constexpr (requires { __v.clone(); }) {
            return __v.clone();
          } else {
            return __v;
          }
        }(d_a0)});
      } else if (std::holds_alternative<CPlus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<CPlus>(_sv.v());
        return cond_expr(
            CPlus{d_a0 ? std::make_unique<LoopifyExpr::cond_expr>(d_a0->clone())
                       : nullptr,
                  d_a1 ? std::make_unique<LoopifyExpr::cond_expr>(d_a1->clone())
                       : nullptr});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<CCond>(_sv.v());
        return cond_expr(
            CCond{d_a0 ? std::make_unique<LoopifyExpr::cond_expr>(d_a0->clone())
                       : nullptr,
                  d_a1 ? std::make_unique<LoopifyExpr::cond_expr>(d_a1->clone())
                       : nullptr,
                  d_a2 ? std::make_unique<LoopifyExpr::cond_expr>(d_a2->clone())
                       : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static cond_expr clit(unsigned int a0) {
      return cond_expr(CLit{std::move(a0)});
    }

    __attribute__((pure)) static cond_expr cplus(const cond_expr &a0,
                                                 const cond_expr &a1) {
      return cond_expr(CPlus{std::make_unique<cond_expr>(a0),
                             std::make_unique<cond_expr>(a1)});
    }

    __attribute__((pure)) static cond_expr
    ccond(const cond_expr &a0, const cond_expr &a1, const cond_expr &a2) {
      return cond_expr(CCond{std::make_unique<cond_expr>(a0),
                             std::make_unique<cond_expr>(a1),
                             std::make_unique<cond_expr>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) cond_expr *operator->() { return this; }

    __attribute__((pure)) const cond_expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = cond_expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    /// depth_cond e computes depth of conditional expression tree.
    __attribute__((pure)) unsigned int depth_cond() const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        cond_expr *_s0;
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
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            _result = 0u;
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get()});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(_Call3{d_a1.get(), d_a0.get()});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = (std::max(_result, _f._s0) + 1);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = (std::max(_result, std::max(_f._s1, _f._s0)) + 1);
        }
      }
      return _result;
    }

    /// eval_cond e evaluates conditional expression.
    __attribute__((pure)) unsigned int eval_cond() const {
      const cond_expr *_self = this;
      auto &&_sv = *(_self);
      if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
        const auto &[d_a0] = std::get<typename cond_expr::CLit>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename cond_expr::CPlus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename cond_expr::CPlus>(_sv.v());
        return ((*(d_a0)).eval_cond() + (*(d_a1)).eval_cond());
      } else {
        const auto &[d_a0, d_a1, d_a2] =
            std::get<typename cond_expr::CCond>(_sv.v());
        if (0u < (*(d_a0)).eval_cond()) {
          return (*(d_a1)).eval_cond();
        } else {
          return (*(d_a2)).eval_cond();
        }
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, cond_expr, T1, cond_expr, T1> F1,
              MapsTo<T1, cond_expr, T1, cond_expr, T1, cond_expr, T1> F2>
    T1 cond_expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        cond_expr *_s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, cond_expr, T1, cond_expr, T1> F1,
              MapsTo<T1, cond_expr, T1, cond_expr, T1, cond_expr, T1> F2>
    T1 cond_expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const cond_expr *_self = this;

      struct _Enter {
        const cond_expr *_self;
      };

      struct _Call1 {
        cond_expr *_s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call2 {
        T1 _s0;
        cond_expr _s1;
        cond_expr _s2;
      };

      struct _Call3 {
        const cond_expr *_s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call4 {
        T1 _s0;
        const cond_expr *_s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      struct _Call5 {
        T1 _s0;
        T1 _s1;
        cond_expr _s2;
        cond_expr _s3;
        cond_expr _s4;
      };

      using _Frame =
          std::variant<_Enter, _Call1, _Call2, _Call3, _Call4, _Call5>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(16);
      _stack.emplace_back(_Enter{_self});
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const cond_expr *_self = _f._self;
          auto &&_sv = *(_self);
          if (std::holds_alternative<typename cond_expr::CLit>(_sv.v())) {
            const auto &[d_a0] = std::get<typename cond_expr::CLit>(_sv.v());
            _result = f(d_a0);
          } else if (std::holds_alternative<typename cond_expr::CPlus>(
                         _sv.v())) {
            const auto &[d_a0, d_a1] =
                std::get<typename cond_expr::CPlus>(_sv.v());
            _stack.emplace_back(_Call1{d_a0.get(), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a1.get()});
          } else {
            const auto &[d_a0, d_a1, d_a2] =
                std::get<typename cond_expr::CCond>(_sv.v());
            _stack.emplace_back(
                _Call3{d_a1.get(), d_a0.get(), *(d_a2), *(d_a1), *(d_a0)});
            _stack.emplace_back(_Enter{d_a2.get()});
          }
        } else if (std::holds_alternative<_Call1>(_frame)) {
          auto _f = std::move(std::get<_Call1>(_frame));
          _stack.emplace_back(_Call2{_result, _f._s1, _f._s2});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call2>(_frame)) {
          auto _f = std::move(std::get<_Call2>(_frame));
          _result = f0(_f._s2, _result, _f._s1, _f._s0);
        } else if (std::holds_alternative<_Call3>(_frame)) {
          auto _f = std::move(std::get<_Call3>(_frame));
          _stack.emplace_back(_Call4{_result, _f._s1, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s0});
        } else if (std::holds_alternative<_Call4>(_frame)) {
          auto _f = std::move(std::get<_Call4>(_frame));
          _stack.emplace_back(_Call5{_f._s0, _result, _f._s2, _f._s3, _f._s4});
          _stack.emplace_back(_Enter{_f._s1});
        } else {
          auto _f = std::move(std::get<_Call5>(_frame));
          _result = f1(_f._s4, _result, _f._s3, _f._s1, _f._s2, _f._s0);
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_EXPR
