#ifndef INCLUDED_LOOPIFY_EXPR_VARIANTS
#define INCLUDED_LOOPIFY_EXPR_VARIANTS

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

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct ListDef {
  template <typename T1> static List<T1> repeat(T1 x, uint64_t n);
};

struct LoopifyExprVariants {
  struct cond_expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Add {
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
    };

    struct Cond {
      std::shared_ptr<cond_expr> a0;
      std::shared_ptr<cond_expr> a1;
      std::shared_ptr<cond_expr> a2;
    };

    using variant_t = std::variant<Lit, Add, Cond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    cond_expr() {}

    explicit cond_expr(Lit _v) : v_(std::move(_v)) {}

    explicit cond_expr(Add _v) : v_(std::move(_v)) {}

    explicit cond_expr(Cond _v) : v_(std::move(_v)) {}

    static cond_expr lit(uint64_t a0) { return cond_expr(Lit{a0}); }

    static cond_expr add(cond_expr a0, cond_expr a1) {
      return cond_expr(Add{std::make_shared<cond_expr>(std::move(a0)),
                           std::make_shared<cond_expr>(std::move(a1))});
    }

    static cond_expr cond(cond_expr a0, cond_expr a1, cond_expr a2) {
      return cond_expr(Cond{std::make_shared<cond_expr>(std::move(a0)),
                            std::make_shared<cond_expr>(std::move(a1)),
                            std::make_shared<cond_expr>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t size_cond() const {
      if (std::holds_alternative<typename cond_expr::Lit>(this->v())) {
        return UINT64_C(1);
      } else if (std::holds_alternative<typename cond_expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::Add>(this->v());
        return ((UINT64_C(1) + a0->size_cond()) + a1->size_cond());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::Cond>(this->v());
        return (((UINT64_C(1) + a0->size_cond()) + a1->size_cond()) +
                a2->size_cond());
      }
    }

    uint64_t eval_cond() const {
      if (std::holds_alternative<typename cond_expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename cond_expr::Lit>(this->v());
        return a0;
      } else if (std::holds_alternative<typename cond_expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::Add>(this->v());
        return (a0->eval_cond() + a1->eval_cond());
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::Cond>(this->v());
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
      if (std::holds_alternative<typename cond_expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename cond_expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename cond_expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::Add>(this->v());
        return f0(*a0, a0->template cond_expr_rec<T1>(f, f0, f1), *a1,
                  a1->template cond_expr_rec<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::Cond>(this->v());
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
      if (std::holds_alternative<typename cond_expr::Lit>(this->v())) {
        const auto &[a0] = std::get<typename cond_expr::Lit>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename cond_expr::Add>(this->v())) {
        const auto &[a0, a1] = std::get<typename cond_expr::Add>(this->v());
        return f0(*a0, a0->template cond_expr_rect<T1>(f, f0, f1), *a1,
                  a1->template cond_expr_rect<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1, a2] =
            std::get<typename cond_expr::Cond>(this->v());
        return f1(*a0, a0->template cond_expr_rect<T1>(f, f0, f1), *a1,
                  a1->template cond_expr_rect<T1>(f, f0, f1), *a2,
                  a2->template cond_expr_rect<T1>(f, f0, f1));
      }
    }
  };

  struct arith_expr {
    // TYPES
    struct ANum {
      uint64_t a0;
    };

    struct AAdd {
      std::shared_ptr<arith_expr> a0;
      std::shared_ptr<arith_expr> a1;
    };

    struct AMul {
      std::shared_ptr<arith_expr> a0;
      std::shared_ptr<arith_expr> a1;
    };

    struct ADiv {
      std::shared_ptr<arith_expr> a0;
      std::shared_ptr<arith_expr> a1;
    };

    using variant_t = std::variant<ANum, AAdd, AMul, ADiv>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    arith_expr() {}

    explicit arith_expr(ANum _v) : v_(std::move(_v)) {}

    explicit arith_expr(AAdd _v) : v_(std::move(_v)) {}

    explicit arith_expr(AMul _v) : v_(std::move(_v)) {}

    explicit arith_expr(ADiv _v) : v_(std::move(_v)) {}

    static arith_expr anum(uint64_t a0) { return arith_expr(ANum{a0}); }

    static arith_expr aadd(arith_expr a0, arith_expr a1) {
      return arith_expr(AAdd{std::make_shared<arith_expr>(std::move(a0)),
                             std::make_shared<arith_expr>(std::move(a1))});
    }

    static arith_expr amul(arith_expr a0, arith_expr a1) {
      return arith_expr(AMul{std::make_shared<arith_expr>(std::move(a0)),
                             std::make_shared<arith_expr>(std::move(a1))});
    }

    static arith_expr adiv(arith_expr a0, arith_expr a1) {
      return arith_expr(ADiv{std::make_shared<arith_expr>(std::move(a0)),
                             std::make_shared<arith_expr>(std::move(a1))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t count_ops() const {
      if (std::holds_alternative<typename arith_expr::ANum>(this->v())) {
        return UINT64_C(0);
      } else if (std::holds_alternative<typename arith_expr::AAdd>(this->v())) {
        const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(this->v());
        return ((UINT64_C(1) + a0->count_ops()) + a1->count_ops());
      } else if (std::holds_alternative<typename arith_expr::AMul>(this->v())) {
        const auto &[a0, a1] = std::get<typename arith_expr::AMul>(this->v());
        return ((UINT64_C(1) + a0->count_ops()) + a1->count_ops());
      } else {
        const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(this->v());
        return ((UINT64_C(1) + a0->count_ops()) + a1->count_ops());
      }
    }

    uint64_t eval_arith() const {
      if (std::holds_alternative<typename arith_expr::ANum>(this->v())) {
        const auto &[a0] = std::get<typename arith_expr::ANum>(this->v());
        return a0;
      } else if (std::holds_alternative<typename arith_expr::AAdd>(this->v())) {
        const auto &[a0, a1] = std::get<typename arith_expr::AAdd>(this->v());
        return (a0->eval_arith() + a1->eval_arith());
      } else if (std::holds_alternative<typename arith_expr::AMul>(this->v())) {
        const auto &[a0, a1] = std::get<typename arith_expr::AMul>(this->v());
        return (a0->eval_arith() * a1->eval_arith());
      } else {
        const auto &[a0, a1] = std::get<typename arith_expr::ADiv>(this->v());
        auto _cs = a1->eval_arith();
        if (_cs <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t n = _cs - 1;
          return ((n + 1) ? a0->eval_arith() / (n + 1) : 0);
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &>
    T1 arith_expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      if (std::holds_alternative<typename arith_expr::ANum>(this->v())) {
        const auto &[a0] = std::get<typename arith_expr::ANum>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename arith_expr::AAdd>(this->v())) {
        const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(this->v());
        return f0(*a2, a2->template arith_expr_rec<T1>(f, f0, f1, f2), *a3,
                  a3->template arith_expr_rec<T1>(f, f0, f1, f2));
      } else if (std::holds_alternative<typename arith_expr::AMul>(this->v())) {
        const auto &[a2, a3] = std::get<typename arith_expr::AMul>(this->v());
        return f1(*a2, a2->template arith_expr_rec<T1>(f, f0, f1, f2), *a3,
                  a3->template arith_expr_rec<T1>(f, f0, f1, f2));
      } else {
        const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(this->v());
        return f2(*a2, a2->template arith_expr_rec<T1>(f, f0, f1, f2), *a3,
                  a3->template arith_expr_rec<T1>(f, f0, f1, f2));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F2 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, arith_expr &, T1 &, arith_expr &,
                                     T1 &>
    T1 arith_expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      if (std::holds_alternative<typename arith_expr::ANum>(this->v())) {
        const auto &[a0] = std::get<typename arith_expr::ANum>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename arith_expr::AAdd>(this->v())) {
        const auto &[a2, a3] = std::get<typename arith_expr::AAdd>(this->v());
        return f0(*a2, a2->template arith_expr_rect<T1>(f, f0, f1, f2), *a3,
                  a3->template arith_expr_rect<T1>(f, f0, f1, f2));
      } else if (std::holds_alternative<typename arith_expr::AMul>(this->v())) {
        const auto &[a2, a3] = std::get<typename arith_expr::AMul>(this->v());
        return f1(*a2, a2->template arith_expr_rect<T1>(f, f0, f1, f2), *a3,
                  a3->template arith_expr_rect<T1>(f, f0, f1, f2));
      } else {
        const auto &[a2, a3] = std::get<typename arith_expr::ADiv>(this->v());
        return f2(*a2, a2->template arith_expr_rect<T1>(f, f0, f1, f2), *a3,
                  a3->template arith_expr_rect<T1>(f, f0, f1, f2));
      }
    }
  };

  struct bool_expr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<bool_expr> a0;
      std::shared_ptr<bool_expr> a1;
    };

    struct BOr {
      std::shared_ptr<bool_expr> a0;
      std::shared_ptr<bool_expr> a1;
    };

    struct BNot {
      std::shared_ptr<bool_expr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bool_expr() {}

    explicit bool_expr(BTrue _v) : v_(_v) {}

    explicit bool_expr(BFalse _v) : v_(_v) {}

    explicit bool_expr(BAnd _v) : v_(std::move(_v)) {}

    explicit bool_expr(BOr _v) : v_(std::move(_v)) {}

    explicit bool_expr(BNot _v) : v_(std::move(_v)) {}

    static bool_expr btrue() { return bool_expr(BTrue{}); }

    static bool_expr bfalse() { return bool_expr(BFalse{}); }

    static bool_expr band(bool_expr a0, bool_expr a1) {
      return bool_expr(BAnd{std::make_shared<bool_expr>(std::move(a0)),
                            std::make_shared<bool_expr>(std::move(a1))});
    }

    static bool_expr bor(bool_expr a0, bool_expr a1) {
      return bool_expr(BOr{std::make_shared<bool_expr>(std::move(a0)),
                           std::make_shared<bool_expr>(std::move(a1))});
    }

    static bool_expr bnot(bool_expr a0) {
      return bool_expr(BNot{std::make_shared<bool_expr>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool_expr simplify_bool() const {
      if (std::holds_alternative<typename bool_expr::BTrue>(this->v())) {
        return bool_expr::btrue();
      } else if (std::holds_alternative<typename bool_expr::BFalse>(
                     this->v())) {
        return bool_expr::bfalse();
      } else if (std::holds_alternative<typename bool_expr::BAnd>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(this->v());
        auto &&_sv0 = a0->simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(*a01, *a11);
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bnot(*a01);
          }
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          return bool_expr::bfalse();
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BAnd>(_sv0.v());
          bool_expr a_ = bool_expr::band(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BOr>(_sv0.v());
          bool_expr a_ = bool_expr::bor(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        } else {
          const auto &[a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          bool_expr a_ = bool_expr::bnot(*a00);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::band(std::move(a_), bool_expr::bnot(*a01));
          }
        }
      } else if (std::holds_alternative<typename bool_expr::BOr>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BOr>(this->v());
        auto &&_sv0 = a0->simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          return bool_expr::btrue();
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return bool_expr::bfalse();
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::band(*a01, *a11);
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(*a01, *a11);
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bnot(*a01);
          }
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BAnd>(_sv0.v());
          bool_expr a_ = bool_expr::band(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BOr>(_sv0.v());
          bool_expr a_ = bool_expr::bor(*a00, *a10);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        } else {
          const auto &[a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          bool_expr a_ = bool_expr::bnot(*a00);
          auto &&_sv1 = a1->simplify_bool();
          if (std::holds_alternative<typename bool_expr::BTrue>(_sv1.v())) {
            return bool_expr::btrue();
          } else if (std::holds_alternative<typename bool_expr::BFalse>(
                         _sv1.v())) {
            return a_;
          } else if (std::holds_alternative<typename bool_expr::BAnd>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BAnd>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::band(*a01, *a11));
          } else if (std::holds_alternative<typename bool_expr::BOr>(
                         _sv1.v())) {
            const auto &[a01, a11] =
                std::get<typename bool_expr::BOr>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bor(*a01, *a11));
          } else {
            const auto &[a01] = std::get<typename bool_expr::BNot>(_sv1.v());
            return bool_expr::bor(std::move(a_), bool_expr::bnot(*a01));
          }
        }
      } else {
        const auto &[a0] = std::get<typename bool_expr::BNot>(this->v());
        auto &&_sv0 = a0->simplify_bool();
        if (std::holds_alternative<typename bool_expr::BTrue>(_sv0.v())) {
          return bool_expr::bfalse();
        } else if (std::holds_alternative<typename bool_expr::BFalse>(
                       _sv0.v())) {
          return bool_expr::btrue();
        } else if (std::holds_alternative<typename bool_expr::BAnd>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BAnd>(_sv0.v());
          return bool_expr::bnot(bool_expr::band(*a00, *a10));
        } else if (std::holds_alternative<typename bool_expr::BOr>(_sv0.v())) {
          const auto &[a00, a10] = std::get<typename bool_expr::BOr>(_sv0.v());
          return bool_expr::bnot(bool_expr::bor(*a00, *a10));
        } else {
          const auto &[a00] = std::get<typename bool_expr::BNot>(_sv0.v());
          return bool_expr::bnot(bool_expr::bnot(*a00));
        }
      }
    }

    bool eval_bool() const {
      if (std::holds_alternative<typename bool_expr::BTrue>(this->v())) {
        return true;
      } else if (std::holds_alternative<typename bool_expr::BFalse>(
                     this->v())) {
        return false;
      } else if (std::holds_alternative<typename bool_expr::BAnd>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(this->v());
        return (a0->eval_bool() && a1->eval_bool());
      } else if (std::holds_alternative<typename bool_expr::BOr>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BOr>(this->v());
        return (a0->eval_bool() || a1->eval_bool());
      } else {
        const auto &[a0] = std::get<typename bool_expr::BNot>(this->v());
        return !(a0->eval_bool());
      }
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F4 &, bool_expr &, T1 &>
    T1 bool_expr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      if (std::holds_alternative<typename bool_expr::BTrue>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename bool_expr::BFalse>(
                     this->v())) {
        return f0;
      } else if (std::holds_alternative<typename bool_expr::BAnd>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(this->v());
        return f1(*a0, a0->template bool_expr_rec<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template bool_expr_rec<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename bool_expr::BOr>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BOr>(this->v());
        return f2(*a0, a0->template bool_expr_rec<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template bool_expr_rec<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[a0] = std::get<typename bool_expr::BNot>(this->v());
        return f3(*a0, a0->template bool_expr_rec<T1>(f, f0, f1, f2, f3));
      }
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, bool_expr &, T1 &, bool_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F4 &, bool_expr &, T1 &>
    T1 bool_expr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      if (std::holds_alternative<typename bool_expr::BTrue>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename bool_expr::BFalse>(
                     this->v())) {
        return f0;
      } else if (std::holds_alternative<typename bool_expr::BAnd>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BAnd>(this->v());
        return f1(*a0, a0->template bool_expr_rect<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template bool_expr_rect<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename bool_expr::BOr>(this->v())) {
        const auto &[a0, a1] = std::get<typename bool_expr::BOr>(this->v());
        return f2(*a0, a0->template bool_expr_rect<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template bool_expr_rect<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[a0] = std::get<typename bool_expr::BNot>(this->v());
        return f3(*a0, a0->template bool_expr_rect<T1>(f, f0, f1, f2, f3));
      }
    }
  };

  struct list_expr {
    // TYPES
    struct LNil {};

    struct LCons {
      uint64_t a0;
      std::shared_ptr<list_expr> a1;
    };

    struct LAppend {
      std::shared_ptr<list_expr> a0;
      std::shared_ptr<list_expr> a1;
    };

    struct LReplicate {
      uint64_t a0;
      uint64_t a1;
    };

    using variant_t = std::variant<LNil, LCons, LAppend, LReplicate>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list_expr() {}

    explicit list_expr(LNil _v) : v_(_v) {}

    explicit list_expr(LCons _v) : v_(std::move(_v)) {}

    explicit list_expr(LAppend _v) : v_(std::move(_v)) {}

    explicit list_expr(LReplicate _v) : v_(std::move(_v)) {}

    static list_expr lnil() { return list_expr(LNil{}); }

    static list_expr lcons(uint64_t a0, list_expr a1) {
      return list_expr(LCons{a0, std::make_shared<list_expr>(std::move(a1))});
    }

    static list_expr lappend(list_expr a0, list_expr a1) {
      return list_expr(LAppend{std::make_shared<list_expr>(std::move(a0)),
                               std::make_shared<list_expr>(std::move(a1))});
    }

    static list_expr lreplicate(uint64_t a0, uint64_t a1) {
      return list_expr(LReplicate{a0, a1});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t list_expr_size() const {
      if (std::holds_alternative<typename list_expr::LCons>(this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LCons>(this->v());
        return (UINT64_C(1) + a1->list_expr_size());
      } else if (std::holds_alternative<typename list_expr::LAppend>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LAppend>(this->v());
        return ((UINT64_C(1) + a0->list_expr_size()) + a1->list_expr_size());
      } else {
        return UINT64_C(1);
      }
    }

    List<uint64_t> eval_list() const {
      if (std::holds_alternative<typename list_expr::LNil>(this->v())) {
        return List<uint64_t>::nil();
      } else if (std::holds_alternative<typename list_expr::LCons>(this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LCons>(this->v());
        return List<uint64_t>::cons(a0, a1->eval_list());
      } else if (std::holds_alternative<typename list_expr::LAppend>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LAppend>(this->v());
        return a0->eval_list().app(a1->eval_list());
      } else {
        const auto &[a0, a1] =
            std::get<typename list_expr::LReplicate>(this->v());
        return ListDef::template repeat<uint64_t>(a1, a0);
      }
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, list_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, list_expr &, T1 &, list_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &>
    T1 list_expr_rec(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      if (std::holds_alternative<typename list_expr::LNil>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename list_expr::LCons>(this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LCons>(this->v());
        return f0(a0, *a1, a1->template list_expr_rec<T1>(f, f0, f1, f2));
      } else if (std::holds_alternative<typename list_expr::LAppend>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LAppend>(this->v());
        return f1(*a0, a0->template list_expr_rec<T1>(f, f0, f1, f2), *a1,
                  a1->template list_expr_rec<T1>(f, f0, f1, f2));
      } else {
        const auto &[a0, a1] =
            std::get<typename list_expr::LReplicate>(this->v());
        return f2(a0, a1);
      }
    }

    template <typename T1, typename F1, typename F2, typename F3>
      requires std::is_invocable_r_v<T1, F1 &, uint64_t &, list_expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, list_expr &, T1 &, list_expr &,
                                     T1 &> &&
               std::is_invocable_r_v<T1, F3 &, uint64_t &, uint64_t &>
    T1 list_expr_rect(T1 f, F1 &&f0, F2 &&f1, F3 &&f2) const {
      if (std::holds_alternative<typename list_expr::LNil>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename list_expr::LCons>(this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LCons>(this->v());
        return f0(a0, *a1, a1->template list_expr_rect<T1>(f, f0, f1, f2));
      } else if (std::holds_alternative<typename list_expr::LAppend>(
                     this->v())) {
        const auto &[a0, a1] = std::get<typename list_expr::LAppend>(this->v());
        return f1(*a0, a0->template list_expr_rect<T1>(f, f0, f1, f2), *a1,
                  a1->template list_expr_rect<T1>(f, f0, f1, f2));
      } else {
        const auto &[a0, a1] =
            std::get<typename list_expr::LReplicate>(this->v());
        return f2(a0, a1);
      }
    }
  };
};

template <typename T1>
List<T1> ListDef::repeat(T1 x,
                         uint64_t n) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

  struct _Enter {
    uint64_t n;
  };

  /// _Resume_k: saves [x], resumes after recursive call with _result.
  struct _Resume_k {
    T1 x;
  };

  using _Frame = std::variant<_Enter, _Resume_k>;
  List<T1> _result{};
  std::vector<_Frame> _stack;
  _stack.reserve(8);
  _stack.emplace_back(_Enter{n});
  /// Loopified repeat: _Enter -> _Resume_k.
  while (!_stack.empty()) {
    _Frame _frame = std::move(_stack.back());
    _stack.pop_back();
    if (std::holds_alternative<_Enter>(_frame)) {
      auto _f = std::move(std::get<_Enter>(_frame));
      uint64_t n = _f.n;
      if (n <= 0) {
        _result = List<T1>::nil();
      } else {
        uint64_t k = n - 1;
        _stack.emplace_back(_Resume_k{x});
        _stack.emplace_back(_Enter{k});
      }
    } else {
      auto _f = std::move(std::get<_Resume_k>(_frame));
      _result = List<T1>::cons(_f.x, _result);
    }
  }
  return _result;
}

#endif // INCLUDED_LOOPIFY_EXPR_VARIANTS
