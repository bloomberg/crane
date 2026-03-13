#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct WhereClause {
  struct Expr {
    // TYPES
    struct Num {
      unsigned int d_a0;
    };

    struct Plus {
      std::shared_ptr<Expr> d_a0;
      std::shared_ptr<Expr> d_a1;
    };

    struct Times {
      std::shared_ptr<Expr> d_a0;
      std::shared_ptr<Expr> d_a1;
    };

    using variant_t = std::variant<Num, Plus, Times>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit Expr(Num _v) : d_v_(std::move(_v)) {}

    explicit Expr(Plus _v) : d_v_(std::move(_v)) {}

    explicit Expr(Times _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<Expr> Num_(unsigned int a0) {
        return std::shared_ptr<Expr>(new Expr(Num{a0}));
      }

      static std::shared_ptr<Expr> Plus_(const std::shared_ptr<Expr> &a0,
                                         const std::shared_ptr<Expr> &a1) {
        return std::shared_ptr<Expr>(new Expr(Plus{a0, a1}));
      }

      static std::shared_ptr<Expr> Times_(const std::shared_ptr<Expr> &a0,
                                          const std::shared_ptr<Expr> &a1) {
        return std::shared_ptr<Expr>(new Expr(Times{a0, a1}));
      }

      static std::unique_ptr<Expr> Num_uptr(unsigned int a0) {
        return std::unique_ptr<Expr>(new Expr(Num{a0}));
      }

      static std::unique_ptr<Expr> Plus_uptr(const std::shared_ptr<Expr> &a0,
                                             const std::shared_ptr<Expr> &a1) {
        return std::unique_ptr<Expr>(new Expr(Plus{a0, a1}));
      }

      static std::unique_ptr<Expr> Times_uptr(const std::shared_ptr<Expr> &a0,
                                              const std::shared_ptr<Expr> &a1) {
        return std::unique_ptr<Expr>(new Expr(Times{a0, a1}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F1,
            MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F2>
  static T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<Expr> &e) {
    return std::visit(Overloaded{[&](const typename Expr::Num _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename Expr::Plus _args) -> T1 {
                                   std::shared_ptr<Expr> e0 = _args.d_a0;
                                   std::shared_ptr<Expr> e1 = _args.d_a1;
                                   return f0(e0, Expr_rect<T1>(f, f0, f1, e0),
                                             e1, Expr_rect<T1>(f, f0, f1, e1));
                                 },
                                 [&](const typename Expr::Times _args) -> T1 {
                                   std::shared_ptr<Expr> e0 = _args.d_a0;
                                   std::shared_ptr<Expr> e1 = _args.d_a1;
                                   return f1(e0, Expr_rect<T1>(f, f0, f1, e0),
                                             e1, Expr_rect<T1>(f, f0, f1, e1));
                                 }},
                      e->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F1,
            MapsTo<T1, std::shared_ptr<Expr>, T1, std::shared_ptr<Expr>, T1> F2>
  static T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1, const std::shared_ptr<Expr> &e) {
    return std::visit(Overloaded{[&](const typename Expr::Num _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename Expr::Plus _args) -> T1 {
                                   std::shared_ptr<Expr> e0 = _args.d_a0;
                                   std::shared_ptr<Expr> e1 = _args.d_a1;
                                   return f0(e0, Expr_rec<T1>(f, f0, f1, e0),
                                             e1, Expr_rec<T1>(f, f0, f1, e1));
                                 },
                                 [&](const typename Expr::Times _args) -> T1 {
                                   std::shared_ptr<Expr> e0 = _args.d_a0;
                                   std::shared_ptr<Expr> e1 = _args.d_a1;
                                   return f1(e0, Expr_rec<T1>(f, f0, f1, e0),
                                             e1, Expr_rec<T1>(f, f0, f1, e1));
                                 }},
                      e->v());
  }

  __attribute__((pure)) static unsigned int
  eval(const std::shared_ptr<Expr> &e);
  __attribute__((pure)) static unsigned int
  expr_size(const std::shared_ptr<Expr> &e);

  struct BExpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<BExpr> d_a0;
      std::shared_ptr<BExpr> d_a1;
    };

    struct BOr {
      std::shared_ptr<BExpr> d_a0;
      std::shared_ptr<BExpr> d_a1;
    };

    struct BNot {
      std::shared_ptr<BExpr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit BExpr(BTrue _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BFalse _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BOr _v) : d_v_(std::move(_v)) {}

    explicit BExpr(BNot _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<BExpr> BTrue_() {
        return std::shared_ptr<BExpr>(new BExpr(BTrue{}));
      }

      static std::shared_ptr<BExpr> BFalse_() {
        return std::shared_ptr<BExpr>(new BExpr(BFalse{}));
      }

      static std::shared_ptr<BExpr> BAnd_(const std::shared_ptr<BExpr> &a0,
                                          const std::shared_ptr<BExpr> &a1) {
        return std::shared_ptr<BExpr>(new BExpr(BAnd{a0, a1}));
      }

      static std::shared_ptr<BExpr> BOr_(const std::shared_ptr<BExpr> &a0,
                                         const std::shared_ptr<BExpr> &a1) {
        return std::shared_ptr<BExpr>(new BExpr(BOr{a0, a1}));
      }

      static std::shared_ptr<BExpr> BNot_(const std::shared_ptr<BExpr> &a0) {
        return std::shared_ptr<BExpr>(new BExpr(BNot{a0}));
      }

      static std::unique_ptr<BExpr> BTrue_uptr() {
        return std::unique_ptr<BExpr>(new BExpr(BTrue{}));
      }

      static std::unique_ptr<BExpr> BFalse_uptr() {
        return std::unique_ptr<BExpr>(new BExpr(BFalse{}));
      }

      static std::unique_ptr<BExpr>
      BAnd_uptr(const std::shared_ptr<BExpr> &a0,
                const std::shared_ptr<BExpr> &a1) {
        return std::unique_ptr<BExpr>(new BExpr(BAnd{a0, a1}));
      }

      static std::unique_ptr<BExpr> BOr_uptr(const std::shared_ptr<BExpr> &a0,
                                             const std::shared_ptr<BExpr> &a1) {
        return std::unique_ptr<BExpr>(new BExpr(BOr{a0, a1}));
      }

      static std::unique_ptr<BExpr>
      BNot_uptr(const std::shared_ptr<BExpr> &a0) {
        return std::unique_ptr<BExpr>(new BExpr(BNot{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F2,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F3,
      MapsTo<T1, std::shared_ptr<BExpr>, T1> F4>
  static T1 BExpr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                       const std::shared_ptr<BExpr> &b) {
    return std::visit(
        Overloaded{[&](const typename BExpr::BTrue _args) -> T1 { return f; },
                   [&](const typename BExpr::BFalse _args) -> T1 { return f0; },
                   [&](const typename BExpr::BAnd _args) -> T1 {
                     std::shared_ptr<BExpr> b0 = _args.d_a0;
                     std::shared_ptr<BExpr> b1 = _args.d_a1;
                     return f1(b0, BExpr_rect<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename BExpr::BOr _args) -> T1 {
                     std::shared_ptr<BExpr> b0 = _args.d_a0;
                     std::shared_ptr<BExpr> b1 = _args.d_a1;
                     return f2(b0, BExpr_rect<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename BExpr::BNot _args) -> T1 {
                     std::shared_ptr<BExpr> b0 = _args.d_a0;
                     return f3(b0, BExpr_rect<T1>(f, f0, f1, f2, f3, b0));
                   }},
        b->v());
  }

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F2,
      MapsTo<T1, std::shared_ptr<BExpr>, T1, std::shared_ptr<BExpr>, T1> F3,
      MapsTo<T1, std::shared_ptr<BExpr>, T1> F4>
  static T1 BExpr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const std::shared_ptr<BExpr> &b) {
    return std::visit(
        Overloaded{[&](const typename BExpr::BTrue _args) -> T1 { return f; },
                   [&](const typename BExpr::BFalse _args) -> T1 { return f0; },
                   [&](const typename BExpr::BAnd _args) -> T1 {
                     std::shared_ptr<BExpr> b0 = _args.d_a0;
                     std::shared_ptr<BExpr> b1 = _args.d_a1;
                     return f1(b0, BExpr_rec<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename BExpr::BOr _args) -> T1 {
                     std::shared_ptr<BExpr> b0 = _args.d_a0;
                     std::shared_ptr<BExpr> b1 = _args.d_a1;
                     return f2(b0, BExpr_rec<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename BExpr::BNot _args) -> T1 {
                     std::shared_ptr<BExpr> b0 = _args.d_a0;
                     return f3(b0, BExpr_rec<T1>(f, f0, f1, f2, f3, b0));
                   }},
        b->v());
  }

  __attribute__((pure)) static bool beval(const std::shared_ptr<BExpr> &e);

  struct AExpr {
    // TYPES
    struct ANum {
      unsigned int d_a0;
    };

    struct APlus {
      std::shared_ptr<AExpr> d_a0;
      std::shared_ptr<AExpr> d_a1;
    };

    struct AIf {
      std::shared_ptr<BExpr> d_a0;
      std::shared_ptr<AExpr> d_a1;
      std::shared_ptr<AExpr> d_a2;
    };

    using variant_t = std::variant<ANum, APlus, AIf>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit AExpr(ANum _v) : d_v_(std::move(_v)) {}

    explicit AExpr(APlus _v) : d_v_(std::move(_v)) {}

    explicit AExpr(AIf _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<AExpr> ANum_(unsigned int a0) {
        return std::shared_ptr<AExpr>(new AExpr(ANum{a0}));
      }

      static std::shared_ptr<AExpr> APlus_(const std::shared_ptr<AExpr> &a0,
                                           const std::shared_ptr<AExpr> &a1) {
        return std::shared_ptr<AExpr>(new AExpr(APlus{a0, a1}));
      }

      static std::shared_ptr<AExpr> AIf_(const std::shared_ptr<BExpr> &a0,
                                         const std::shared_ptr<AExpr> &a1,
                                         const std::shared_ptr<AExpr> &a2) {
        return std::shared_ptr<AExpr>(new AExpr(AIf{a0, a1, a2}));
      }

      static std::unique_ptr<AExpr> ANum_uptr(unsigned int a0) {
        return std::unique_ptr<AExpr>(new AExpr(ANum{a0}));
      }

      static std::unique_ptr<AExpr>
      APlus_uptr(const std::shared_ptr<AExpr> &a0,
                 const std::shared_ptr<AExpr> &a1) {
        return std::unique_ptr<AExpr>(new AExpr(APlus{a0, a1}));
      }

      static std::unique_ptr<AExpr> AIf_uptr(const std::shared_ptr<BExpr> &a0,
                                             const std::shared_ptr<AExpr> &a1,
                                             const std::shared_ptr<AExpr> &a2) {
        return std::unique_ptr<AExpr>(new AExpr(AIf{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<AExpr>, T1, std::shared_ptr<AExpr>, T1> F1,
      MapsTo<T1, std::shared_ptr<BExpr>, std::shared_ptr<AExpr>, T1,
             std::shared_ptr<AExpr>, T1>
          F2>
  static T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1,
                       const std::shared_ptr<AExpr> &a) {
    return std::visit(Overloaded{[&](const typename AExpr::ANum _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename AExpr::APlus _args) -> T1 {
                                   std::shared_ptr<AExpr> a0 = _args.d_a0;
                                   std::shared_ptr<AExpr> a1 = _args.d_a1;
                                   return f0(a0, AExpr_rect<T1>(f, f0, f1, a0),
                                             a1, AExpr_rect<T1>(f, f0, f1, a1));
                                 },
                                 [&](const typename AExpr::AIf _args) -> T1 {
                                   std::shared_ptr<BExpr> b = _args.d_a0;
                                   std::shared_ptr<AExpr> a0 = _args.d_a1;
                                   std::shared_ptr<AExpr> a1 = _args.d_a2;
                                   return f1(std::move(b), a0,
                                             AExpr_rect<T1>(f, f0, f1, a0), a1,
                                             AExpr_rect<T1>(f, f0, f1, a1));
                                 }},
                      a->v());
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<AExpr>, T1, std::shared_ptr<AExpr>, T1> F1,
      MapsTo<T1, std::shared_ptr<BExpr>, std::shared_ptr<AExpr>, T1,
             std::shared_ptr<AExpr>, T1>
          F2>
  static T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<AExpr> &a) {
    return std::visit(Overloaded{[&](const typename AExpr::ANum _args) -> T1 {
                                   unsigned int n = _args.d_a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename AExpr::APlus _args) -> T1 {
                                   std::shared_ptr<AExpr> a0 = _args.d_a0;
                                   std::shared_ptr<AExpr> a1 = _args.d_a1;
                                   return f0(a0, AExpr_rec<T1>(f, f0, f1, a0),
                                             a1, AExpr_rec<T1>(f, f0, f1, a1));
                                 },
                                 [&](const typename AExpr::AIf _args) -> T1 {
                                   std::shared_ptr<BExpr> b = _args.d_a0;
                                   std::shared_ptr<AExpr> a0 = _args.d_a1;
                                   std::shared_ptr<AExpr> a1 = _args.d_a2;
                                   return f1(std::move(b), a0,
                                             AExpr_rec<T1>(f, f0, f1, a0), a1,
                                             AExpr_rec<T1>(f, f0, f1, a1));
                                 }},
                      a->v());
  }

  __attribute__((pure)) static unsigned int
  aeval(const std::shared_ptr<AExpr> &e);
  static inline const unsigned int test_eval_plus =
      eval(Expr::ctor::Plus_(Expr::ctor::Num_(3u), Expr::ctor::Num_(4u)));
  static inline const unsigned int test_eval_times =
      eval(Expr::ctor::Times_(Expr::ctor::Num_(5u), Expr::ctor::Num_(6u)));
  static inline const unsigned int test_eval_nested = eval(Expr::ctor::Plus_(
      Expr::ctor::Times_(Expr::ctor::Num_(2u), Expr::ctor::Num_(3u)),
      Expr::ctor::Num_(1u)));
  static inline const unsigned int test_size = expr_size(Expr::ctor::Plus_(
      Expr::ctor::Times_(Expr::ctor::Num_(2u), Expr::ctor::Num_(3u)),
      Expr::ctor::Num_(1u)));
  static inline const bool test_beval = beval(BExpr::ctor::BAnd_(
      BExpr::ctor::BTrue_(), BExpr::ctor::BNot_(BExpr::ctor::BFalse_())));
  static inline const unsigned int test_aeval = aeval(AExpr::ctor::AIf_(
      BExpr::ctor::BAnd_(BExpr::ctor::BTrue_(), BExpr::ctor::BTrue_()),
      AExpr::ctor::ANum_(10u), AExpr::ctor::ANum_(20u)));
};

#endif // INCLUDED_WHERE_CLAUSE
