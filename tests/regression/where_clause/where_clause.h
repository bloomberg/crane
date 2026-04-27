#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct WhereClause {
  struct Expr {
    // TYPES
    struct Num {
      unsigned int d_a0;
    };

    struct Plus {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    struct Times {
      std::unique_ptr<Expr> d_a0;
      std::unique_ptr<Expr> d_a1;
    };

    using variant_t = std::variant<Num, Plus, Times>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    Expr() {}

    explicit Expr(Num _v) : d_v_(std::move(_v)) {}

    explicit Expr(Plus _v) : d_v_(std::move(_v)) {}

    explicit Expr(Times _v) : d_v_(std::move(_v)) {}

    Expr(const Expr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    Expr(Expr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) Expr &operator=(const Expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) Expr &operator=(Expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) Expr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Num>(_sv.v())) {
        const auto &[d_a0] = std::get<Num>(_sv.v());
        return Expr(Num{d_a0});
      } else if (std::holds_alternative<Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<Plus>(_sv.v());
        return Expr(Plus{
            d_a0 ? std::make_unique<WhereClause::Expr>(d_a0->clone()) : nullptr,
            d_a1 ? std::make_unique<WhereClause::Expr>(d_a1->clone())
                 : nullptr});
      } else {
        const auto &[d_a0, d_a1] = std::get<Times>(_sv.v());
        return Expr(Times{
            d_a0 ? std::make_unique<WhereClause::Expr>(d_a0->clone()) : nullptr,
            d_a1 ? std::make_unique<WhereClause::Expr>(d_a1->clone())
                 : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static Expr num(unsigned int a0) {
      return Expr(Num{std::move(a0)});
    }

    __attribute__((pure)) static Expr plus(const Expr &a0, const Expr &a1) {
      return Expr(Plus{std::make_unique<Expr>(a0), std::make_unique<Expr>(a1)});
    }

    __attribute__((pure)) static Expr times(const Expr &a0, const Expr &a1) {
      return Expr(
          Times{std::make_unique<Expr>(a0), std::make_unique<Expr>(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) Expr *operator->() { return this; }

    __attribute__((pure)) const Expr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = Expr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int expr_size() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
        return 1u;
      } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Plus>(_sv.v());
        return ((1u + (*(d_a0)).expr_size()) + (*(d_a1)).expr_size());
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Times>(_sv.v());
        return ((1u + (*(d_a0)).expr_size()) + (*(d_a1)).expr_size());
      }
    }

    __attribute__((pure)) unsigned int eval() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::Num>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Plus>(_sv.v());
        return ((*(d_a0)).eval() + (*(d_a1)).eval());
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Times>(_sv.v());
        return ((*(d_a0)).eval() * (*(d_a1)).eval());
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, Expr, T1, Expr, T1> F1,
              MapsTo<T1, Expr, T1, Expr, T1> F2>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::Num>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Plus>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1), *(d_a1),
                  (*(d_a1)).template Expr_rec<T1>(f, f0, f1));
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Times>(_sv.v());
        return f1(*(d_a0), (*(d_a0)).template Expr_rec<T1>(f, f0, f1), *(d_a1),
                  (*(d_a1)).template Expr_rec<T1>(f, f0, f1));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, Expr, T1, Expr, T1> F1,
              MapsTo<T1, Expr, T1, Expr, T1> F2>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
        const auto &[d_a0] = std::get<typename Expr::Num>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Plus>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1), *(d_a1),
                  (*(d_a1)).template Expr_rect<T1>(f, f0, f1));
      } else {
        const auto &[d_a0, d_a1] = std::get<typename Expr::Times>(_sv.v());
        return f1(*(d_a0), (*(d_a0)).template Expr_rect<T1>(f, f0, f1), *(d_a1),
                  (*(d_a1)).template Expr_rect<T1>(f, f0, f1));
      }
    }
  };

  struct BExpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::unique_ptr<BExpr> d_a0;
      std::unique_ptr<BExpr> d_a1;
    };

    struct BOr {
      std::unique_ptr<BExpr> d_a0;
      std::unique_ptr<BExpr> d_a1;
    };

    struct BNot {
      std::unique_ptr<BExpr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    BExpr() {}

    explicit BExpr(BTrue _v) : d_v_(_v) {}

    explicit BExpr(BFalse _v) : d_v_(_v) {}

    explicit BExpr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BOr _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BNot _v) : d_v_(std::move(_v)) {}

    BExpr(const BExpr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    BExpr(BExpr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) BExpr &operator=(const BExpr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) BExpr &operator=(BExpr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) BExpr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<BTrue>(_sv.v())) {
        return BExpr(BTrue{});
      } else if (std::holds_alternative<BFalse>(_sv.v())) {
        return BExpr(BFalse{});
      } else if (std::holds_alternative<BAnd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BAnd>(_sv.v());
        return BExpr(
            BAnd{d_a0 ? std::make_unique<WhereClause::BExpr>(d_a0->clone())
                      : nullptr,
                 d_a1 ? std::make_unique<WhereClause::BExpr>(d_a1->clone())
                      : nullptr});
      } else if (std::holds_alternative<BOr>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BOr>(_sv.v());
        return BExpr(
            BOr{d_a0 ? std::make_unique<WhereClause::BExpr>(d_a0->clone())
                     : nullptr,
                d_a1 ? std::make_unique<WhereClause::BExpr>(d_a1->clone())
                     : nullptr});
      } else {
        const auto &[d_a0] = std::get<BNot>(_sv.v());
        return BExpr(
            BNot{d_a0 ? std::make_unique<WhereClause::BExpr>(d_a0->clone())
                      : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static BExpr btrue() { return BExpr(BTrue{}); }

    __attribute__((pure)) static BExpr bfalse() { return BExpr(BFalse{}); }

    __attribute__((pure)) static BExpr band(const BExpr &a0, const BExpr &a1) {
      return BExpr(
          BAnd{std::make_unique<BExpr>(a0), std::make_unique<BExpr>(a1)});
    }

    __attribute__((pure)) static BExpr bor(const BExpr &a0, const BExpr &a1) {
      return BExpr(
          BOr{std::make_unique<BExpr>(a0), std::make_unique<BExpr>(a1)});
    }

    __attribute__((pure)) static BExpr bnot(const BExpr &a0) {
      return BExpr(BNot{std::make_unique<BExpr>(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) BExpr *operator->() { return this; }

    __attribute__((pure)) const BExpr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = BExpr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) bool beval() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
        return true;
      } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
        return false;
      } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename BExpr::BAnd>(_sv.v());
        return ((*(d_a0)).beval() && (*(d_a1)).beval());
      } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename BExpr::BOr>(_sv.v());
        return ((*(d_a0)).beval() || (*(d_a1)).beval());
      } else {
        const auto &[d_a0] = std::get<typename BExpr::BNot>(_sv.v());
        return !((*(d_a0)).beval());
      }
    }

    template <typename T1, MapsTo<T1, BExpr, T1, BExpr, T1> F2,
              MapsTo<T1, BExpr, T1, BExpr, T1> F3, MapsTo<T1, BExpr, T1> F4>
    T1 BExpr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
        return f0;
      } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename BExpr::BAnd>(_sv.v());
        return f1(*(d_a0), (*(d_a0)).template BExpr_rec<T1>(f, f0, f1, f2, f3),
                  *(d_a1), (*(d_a1)).template BExpr_rec<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename BExpr::BOr>(_sv.v());
        return f2(*(d_a0), (*(d_a0)).template BExpr_rec<T1>(f, f0, f1, f2, f3),
                  *(d_a1), (*(d_a1)).template BExpr_rec<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[d_a0] = std::get<typename BExpr::BNot>(_sv.v());
        return f3(*(d_a0), (*(d_a0)).template BExpr_rec<T1>(f, f0, f1, f2, f3));
      }
    }

    template <typename T1, MapsTo<T1, BExpr, T1, BExpr, T1> F2,
              MapsTo<T1, BExpr, T1, BExpr, T1> F3, MapsTo<T1, BExpr, T1> F4>
    T1 BExpr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
        return f;
      } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
        return f0;
      } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename BExpr::BAnd>(_sv.v());
        return f1(*(d_a0), (*(d_a0)).template BExpr_rect<T1>(f, f0, f1, f2, f3),
                  *(d_a1),
                  (*(d_a1)).template BExpr_rect<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename BExpr::BOr>(_sv.v());
        return f2(*(d_a0), (*(d_a0)).template BExpr_rect<T1>(f, f0, f1, f2, f3),
                  *(d_a1),
                  (*(d_a1)).template BExpr_rect<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[d_a0] = std::get<typename BExpr::BNot>(_sv.v());
        return f3(*(d_a0),
                  (*(d_a0)).template BExpr_rect<T1>(f, f0, f1, f2, f3));
      }
    }
  };

  struct AExpr {
    // TYPES
    struct ANum {
      unsigned int d_a0;
    };

    struct APlus {
      std::unique_ptr<AExpr> d_a0;
      std::unique_ptr<AExpr> d_a1;
    };

    struct AIf {
      BExpr d_a0;
      std::unique_ptr<AExpr> d_a1;
      std::unique_ptr<AExpr> d_a2;
    };

    using variant_t = std::variant<ANum, APlus, AIf>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    AExpr() {}

    explicit AExpr(ANum _v) : d_v_(std::move(_v)) {}

    explicit AExpr(APlus _v) : d_v_(std::move(_v)) {}

    explicit AExpr(AIf _v) : d_v_(std::move(_v)) {}

    AExpr(const AExpr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    AExpr(AExpr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) AExpr &operator=(const AExpr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) AExpr &operator=(AExpr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) AExpr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<ANum>(_sv.v())) {
        const auto &[d_a0] = std::get<ANum>(_sv.v());
        return AExpr(ANum{d_a0});
      } else if (std::holds_alternative<APlus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<APlus>(_sv.v());
        return AExpr(
            APlus{d_a0 ? std::make_unique<WhereClause::AExpr>(d_a0->clone())
                       : nullptr,
                  d_a1 ? std::make_unique<WhereClause::AExpr>(d_a1->clone())
                       : nullptr});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<AIf>(_sv.v());
        return AExpr(
            AIf{d_a0.clone(),
                d_a1 ? std::make_unique<WhereClause::AExpr>(d_a1->clone())
                     : nullptr,
                d_a2 ? std::make_unique<WhereClause::AExpr>(d_a2->clone())
                     : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static AExpr anum(unsigned int a0) {
      return AExpr(ANum{std::move(a0)});
    }

    __attribute__((pure)) static AExpr aplus(const AExpr &a0, const AExpr &a1) {
      return AExpr(
          APlus{std::make_unique<AExpr>(a0), std::make_unique<AExpr>(a1)});
    }

    __attribute__((pure)) static AExpr aif(BExpr a0, const AExpr &a1,
                                           const AExpr &a2) {
      return AExpr(AIf{std::move(a0), std::make_unique<AExpr>(a1),
                       std::make_unique<AExpr>(a2)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) AExpr *operator->() { return this; }

    __attribute__((pure)) const AExpr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = AExpr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    __attribute__((pure)) unsigned int aeval() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
        const auto &[d_a0] = std::get<typename AExpr::ANum>(_sv.v());
        return d_a0;
      } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename AExpr::APlus>(_sv.v());
        return ((*(d_a0)).aeval() + (*(d_a1)).aeval());
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename AExpr::AIf>(_sv.v());
        if (d_a0.beval()) {
          return (*(d_a1)).aeval();
        } else {
          return (*(d_a2)).aeval();
        }
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, AExpr, T1, AExpr, T1> F1,
              MapsTo<T1, BExpr, AExpr, T1, AExpr, T1> F2>
    T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
        const auto &[d_a0] = std::get<typename AExpr::ANum>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename AExpr::APlus>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template AExpr_rec<T1>(f, f0, f1), *(d_a1),
                  (*(d_a1)).template AExpr_rec<T1>(f, f0, f1));
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename AExpr::AIf>(_sv.v());
        return f1(d_a0, *(d_a1), (*(d_a1)).template AExpr_rec<T1>(f, f0, f1),
                  *(d_a2), (*(d_a2)).template AExpr_rec<T1>(f, f0, f1));
      }
    }

    template <typename T1, MapsTo<T1, unsigned int> F0,
              MapsTo<T1, AExpr, T1, AExpr, T1> F1,
              MapsTo<T1, BExpr, AExpr, T1, AExpr, T1> F2>
    T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      auto &&_sv = *(this);
      if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
        const auto &[d_a0] = std::get<typename AExpr::ANum>(_sv.v());
        return f(d_a0);
      } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<typename AExpr::APlus>(_sv.v());
        return f0(*(d_a0), (*(d_a0)).template AExpr_rect<T1>(f, f0, f1),
                  *(d_a1), (*(d_a1)).template AExpr_rect<T1>(f, f0, f1));
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<typename AExpr::AIf>(_sv.v());
        return f1(d_a0, *(d_a1), (*(d_a1)).template AExpr_rect<T1>(f, f0, f1),
                  *(d_a2), (*(d_a2)).template AExpr_rect<T1>(f, f0, f1));
      }
    }
  };

  static inline const unsigned int test_eval_plus =
      Expr::plus(Expr::num(3u), Expr::num(4u)).eval();
  static inline const unsigned int test_eval_times =
      Expr::times(Expr::num(5u), Expr::num(6u)).eval();
  static inline const unsigned int test_eval_nested =
      Expr::plus(Expr::times(Expr::num(2u), Expr::num(3u)), Expr::num(1u))
          .eval();
  static inline const unsigned int test_size =
      Expr::plus(Expr::times(Expr::num(2u), Expr::num(3u)), Expr::num(1u))
          .expr_size();
  static inline const bool test_beval =
      BExpr::band(BExpr::btrue(), BExpr::bnot(BExpr::bfalse())).beval();
  static inline const unsigned int test_aeval =
      AExpr::aif(BExpr::band(BExpr::btrue(), BExpr::btrue()), AExpr::anum(10u),
                 AExpr::anum(20u))
          .aeval();
};

#endif // INCLUDED_WHERE_CLAUSE
