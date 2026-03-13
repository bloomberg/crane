#ifndef INCLUDED_LARGE_MUTUAL
#define INCLUDED_LARGE_MUTUAL

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

struct LargeMutual {
  struct stmt;
  struct expr;
  struct bexpr;

  struct stmt {
    // TYPES
    struct SAssign {
      unsigned int d_a0;
      std::shared_ptr<expr> d_a1;
    };

    struct SSeq {
      std::shared_ptr<stmt> d_a0;
      std::shared_ptr<stmt> d_a1;
    };

    struct SIf {
      std::shared_ptr<bexpr> d_a0;
      std::shared_ptr<stmt> d_a1;
      std::shared_ptr<stmt> d_a2;
    };

    struct SWhile {
      std::shared_ptr<bexpr> d_a0;
      std::shared_ptr<stmt> d_a1;
    };

    struct SSkip {};

    using variant_t = std::variant<SAssign, SSeq, SIf, SWhile, SSkip>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit stmt(SAssign _v) : d_v_(std::move(_v)) {}

    explicit stmt(SSeq _v) : d_v_(std::move(_v)) {}

    explicit stmt(SIf _v) : d_v_(std::move(_v)) {}

    explicit stmt(SWhile _v) : d_v_(std::move(_v)) {}

    explicit stmt(SSkip _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<stmt> SAssign_(unsigned int a0,
                                            const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<stmt>(new stmt(SAssign{a0, a1}));
      }

      static std::shared_ptr<stmt> SSeq_(const std::shared_ptr<stmt> &a0,
                                         const std::shared_ptr<stmt> &a1) {
        return std::shared_ptr<stmt>(new stmt(SSeq{a0, a1}));
      }

      static std::shared_ptr<stmt> SIf_(const std::shared_ptr<bexpr> &a0,
                                        const std::shared_ptr<stmt> &a1,
                                        const std::shared_ptr<stmt> &a2) {
        return std::shared_ptr<stmt>(new stmt(SIf{a0, a1, a2}));
      }

      static std::shared_ptr<stmt> SWhile_(const std::shared_ptr<bexpr> &a0,
                                           const std::shared_ptr<stmt> &a1) {
        return std::shared_ptr<stmt>(new stmt(SWhile{a0, a1}));
      }

      static std::shared_ptr<stmt> SSkip_() {
        return std::shared_ptr<stmt>(new stmt(SSkip{}));
      }

      static std::unique_ptr<stmt>
      SAssign_uptr(unsigned int a0, const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<stmt>(new stmt(SAssign{a0, a1}));
      }

      static std::unique_ptr<stmt> SSeq_uptr(const std::shared_ptr<stmt> &a0,
                                             const std::shared_ptr<stmt> &a1) {
        return std::unique_ptr<stmt>(new stmt(SSeq{a0, a1}));
      }

      static std::unique_ptr<stmt> SIf_uptr(const std::shared_ptr<bexpr> &a0,
                                            const std::shared_ptr<stmt> &a1,
                                            const std::shared_ptr<stmt> &a2) {
        return std::unique_ptr<stmt>(new stmt(SIf{a0, a1, a2}));
      }

      static std::unique_ptr<stmt>
      SWhile_uptr(const std::shared_ptr<bexpr> &a0,
                  const std::shared_ptr<stmt> &a1) {
        return std::unique_ptr<stmt>(new stmt(SWhile{a0, a1}));
      }

      static std::unique_ptr<stmt> SSkip_uptr() {
        return std::unique_ptr<stmt>(new stmt(SSkip{}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct expr {
    // TYPES
    struct ENum {
      unsigned int d_a0;
    };

    struct EVar {
      unsigned int d_a0;
    };

    struct EAdd {
      std::shared_ptr<expr> d_a0;
      std::shared_ptr<expr> d_a1;
    };

    struct EMul {
      std::shared_ptr<expr> d_a0;
      std::shared_ptr<expr> d_a1;
    };

    struct ECond {
      std::shared_ptr<bexpr> d_a0;
      std::shared_ptr<expr> d_a1;
      std::shared_ptr<expr> d_a2;
    };

    using variant_t = std::variant<ENum, EVar, EAdd, EMul, ECond>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit expr(ENum _v) : d_v_(std::move(_v)) {}

    explicit expr(EVar _v) : d_v_(std::move(_v)) {}

    explicit expr(EAdd _v) : d_v_(std::move(_v)) {}

    explicit expr(EMul _v) : d_v_(std::move(_v)) {}

    explicit expr(ECond _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<expr> ENum_(unsigned int a0) {
        return std::shared_ptr<expr>(new expr(ENum{a0}));
      }

      static std::shared_ptr<expr> EVar_(unsigned int a0) {
        return std::shared_ptr<expr>(new expr(EVar{a0}));
      }

      static std::shared_ptr<expr> EAdd_(const std::shared_ptr<expr> &a0,
                                         const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<expr>(new expr(EAdd{a0, a1}));
      }

      static std::shared_ptr<expr> EMul_(const std::shared_ptr<expr> &a0,
                                         const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<expr>(new expr(EMul{a0, a1}));
      }

      static std::shared_ptr<expr> ECond_(const std::shared_ptr<bexpr> &a0,
                                          const std::shared_ptr<expr> &a1,
                                          const std::shared_ptr<expr> &a2) {
        return std::shared_ptr<expr>(new expr(ECond{a0, a1, a2}));
      }

      static std::unique_ptr<expr> ENum_uptr(unsigned int a0) {
        return std::unique_ptr<expr>(new expr(ENum{a0}));
      }

      static std::unique_ptr<expr> EVar_uptr(unsigned int a0) {
        return std::unique_ptr<expr>(new expr(EVar{a0}));
      }

      static std::unique_ptr<expr> EAdd_uptr(const std::shared_ptr<expr> &a0,
                                             const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<expr>(new expr(EAdd{a0, a1}));
      }

      static std::unique_ptr<expr> EMul_uptr(const std::shared_ptr<expr> &a0,
                                             const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<expr>(new expr(EMul{a0, a1}));
      }

      static std::unique_ptr<expr> ECond_uptr(const std::shared_ptr<bexpr> &a0,
                                              const std::shared_ptr<expr> &a1,
                                              const std::shared_ptr<expr> &a2) {
        return std::unique_ptr<expr>(new expr(ECond{a0, a1, a2}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  struct bexpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BEq {
      std::shared_ptr<expr> d_a0;
      std::shared_ptr<expr> d_a1;
    };

    struct BLt {
      std::shared_ptr<expr> d_a0;
      std::shared_ptr<expr> d_a1;
    };

    struct BAnd {
      std::shared_ptr<bexpr> d_a0;
      std::shared_ptr<bexpr> d_a1;
    };

    struct BOr {
      std::shared_ptr<bexpr> d_a0;
      std::shared_ptr<bexpr> d_a1;
    };

    struct BNot {
      std::shared_ptr<bexpr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BEq, BLt, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit bexpr(BTrue _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BFalse _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BEq _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BLt _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BOr _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BNot _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<bexpr> BTrue_() {
        return std::shared_ptr<bexpr>(new bexpr(BTrue{}));
      }

      static std::shared_ptr<bexpr> BFalse_() {
        return std::shared_ptr<bexpr>(new bexpr(BFalse{}));
      }

      static std::shared_ptr<bexpr> BEq_(const std::shared_ptr<expr> &a0,
                                         const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<bexpr>(new bexpr(BEq{a0, a1}));
      }

      static std::shared_ptr<bexpr> BLt_(const std::shared_ptr<expr> &a0,
                                         const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<bexpr>(new bexpr(BLt{a0, a1}));
      }

      static std::shared_ptr<bexpr> BAnd_(const std::shared_ptr<bexpr> &a0,
                                          const std::shared_ptr<bexpr> &a1) {
        return std::shared_ptr<bexpr>(new bexpr(BAnd{a0, a1}));
      }

      static std::shared_ptr<bexpr> BOr_(const std::shared_ptr<bexpr> &a0,
                                         const std::shared_ptr<bexpr> &a1) {
        return std::shared_ptr<bexpr>(new bexpr(BOr{a0, a1}));
      }

      static std::shared_ptr<bexpr> BNot_(const std::shared_ptr<bexpr> &a0) {
        return std::shared_ptr<bexpr>(new bexpr(BNot{a0}));
      }

      static std::unique_ptr<bexpr> BTrue_uptr() {
        return std::unique_ptr<bexpr>(new bexpr(BTrue{}));
      }

      static std::unique_ptr<bexpr> BFalse_uptr() {
        return std::unique_ptr<bexpr>(new bexpr(BFalse{}));
      }

      static std::unique_ptr<bexpr> BEq_uptr(const std::shared_ptr<expr> &a0,
                                             const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<bexpr>(new bexpr(BEq{a0, a1}));
      }

      static std::unique_ptr<bexpr> BLt_uptr(const std::shared_ptr<expr> &a0,
                                             const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<bexpr>(new bexpr(BLt{a0, a1}));
      }

      static std::unique_ptr<bexpr>
      BAnd_uptr(const std::shared_ptr<bexpr> &a0,
                const std::shared_ptr<bexpr> &a1) {
        return std::unique_ptr<bexpr>(new bexpr(BAnd{a0, a1}));
      }

      static std::unique_ptr<bexpr> BOr_uptr(const std::shared_ptr<bexpr> &a0,
                                             const std::shared_ptr<bexpr> &a1) {
        return std::unique_ptr<bexpr>(new bexpr(BOr{a0, a1}));
      }

      static std::unique_ptr<bexpr>
      BNot_uptr(const std::shared_ptr<bexpr> &a0) {
        return std::unique_ptr<bexpr>(new bexpr(BNot{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, std::shared_ptr<expr>> F0,
            MapsTo<T1, std::shared_ptr<stmt>, T1, std::shared_ptr<stmt>, T1> F1,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<stmt>, T1,
                   std::shared_ptr<stmt>, T1>
                F2,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<stmt>, T1> F3>
  static T1 stmt_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, const T1 f3,
                      const std::shared_ptr<stmt> &s) {
    return std::visit(
        Overloaded{
            [&](const typename stmt::SAssign _args) -> T1 {
              unsigned int n = _args.d_a0;
              std::shared_ptr<expr> e = _args.d_a1;
              return f(std::move(n), std::move(e));
            },
            [&](const typename stmt::SSeq _args) -> T1 {
              std::shared_ptr<stmt> s0 = _args.d_a0;
              std::shared_ptr<stmt> s1 = _args.d_a1;
              return f0(s0, stmt_rect<T1>(f, f0, f1, f2, f3, s0), s1,
                        stmt_rect<T1>(f, f0, f1, f2, f3, s1));
            },
            [&](const typename stmt::SIf _args) -> T1 {
              std::shared_ptr<bexpr> b = _args.d_a0;
              std::shared_ptr<stmt> s0 = _args.d_a1;
              std::shared_ptr<stmt> s1 = _args.d_a2;
              return f1(std::move(b), s0, stmt_rect<T1>(f, f0, f1, f2, f3, s0),
                        s1, stmt_rect<T1>(f, f0, f1, f2, f3, s1));
            },
            [&](const typename stmt::SWhile _args) -> T1 {
              std::shared_ptr<bexpr> b = _args.d_a0;
              std::shared_ptr<stmt> s0 = _args.d_a1;
              return f2(std::move(b), s0, stmt_rect<T1>(f, f0, f1, f2, f3, s0));
            },
            [&](const typename stmt::SSkip _args) -> T1 { return f3; }},
        s->v());
  }

  template <typename T1, MapsTo<T1, unsigned int, std::shared_ptr<expr>> F0,
            MapsTo<T1, std::shared_ptr<stmt>, T1, std::shared_ptr<stmt>, T1> F1,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<stmt>, T1,
                   std::shared_ptr<stmt>, T1>
                F2,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<stmt>, T1> F3>
  static T1 stmt_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, const T1 f3,
                     const std::shared_ptr<stmt> &s) {
    return std::visit(
        Overloaded{
            [&](const typename stmt::SAssign _args) -> T1 {
              unsigned int n = _args.d_a0;
              std::shared_ptr<expr> e = _args.d_a1;
              return f(std::move(n), std::move(e));
            },
            [&](const typename stmt::SSeq _args) -> T1 {
              std::shared_ptr<stmt> s0 = _args.d_a0;
              std::shared_ptr<stmt> s1 = _args.d_a1;
              return f0(s0, stmt_rec<T1>(f, f0, f1, f2, f3, s0), s1,
                        stmt_rec<T1>(f, f0, f1, f2, f3, s1));
            },
            [&](const typename stmt::SIf _args) -> T1 {
              std::shared_ptr<bexpr> b = _args.d_a0;
              std::shared_ptr<stmt> s0 = _args.d_a1;
              std::shared_ptr<stmt> s1 = _args.d_a2;
              return f1(std::move(b), s0, stmt_rec<T1>(f, f0, f1, f2, f3, s0),
                        s1, stmt_rec<T1>(f, f0, f1, f2, f3, s1));
            },
            [&](const typename stmt::SWhile _args) -> T1 {
              std::shared_ptr<bexpr> b = _args.d_a0;
              std::shared_ptr<stmt> s0 = _args.d_a1;
              return f2(std::move(b), s0, stmt_rec<T1>(f, f0, f1, f2, f3, s0));
            },
            [&](const typename stmt::SSkip _args) -> T1 { return f3; }},
        s->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F3,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<expr>, T1,
                   std::shared_ptr<expr>, T1>
                F4>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const std::shared_ptr<expr> &e) {
    return std::visit(
        Overloaded{[&](const typename expr::ENum _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename expr::EVar _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename expr::EAdd _args) -> T1 {
                     std::shared_ptr<expr> e0 = _args.d_a0;
                     std::shared_ptr<expr> e1 = _args.d_a1;
                     return f1(e0, expr_rect<T1>(f, f0, f1, f2, f3, e0), e1,
                               expr_rect<T1>(f, f0, f1, f2, f3, e1));
                   },
                   [&](const typename expr::EMul _args) -> T1 {
                     std::shared_ptr<expr> e0 = _args.d_a0;
                     std::shared_ptr<expr> e1 = _args.d_a1;
                     return f2(e0, expr_rect<T1>(f, f0, f1, f2, f3, e0), e1,
                               expr_rect<T1>(f, f0, f1, f2, f3, e1));
                   },
                   [&](const typename expr::ECond _args) -> T1 {
                     std::shared_ptr<bexpr> b = _args.d_a0;
                     std::shared_ptr<expr> e0 = _args.d_a1;
                     std::shared_ptr<expr> e1 = _args.d_a2;
                     return f3(std::move(b), e0,
                               expr_rect<T1>(f, f0, f1, f2, f3, e0), e1,
                               expr_rect<T1>(f, f0, f1, f2, f3, e1));
                   }},
        e->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F3,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<expr>, T1,
                   std::shared_ptr<expr>, T1>
                F4>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                     const std::shared_ptr<expr> &e) {
    return std::visit(
        Overloaded{[&](const typename expr::ENum _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f(std::move(n));
                   },
                   [&](const typename expr::EVar _args) -> T1 {
                     unsigned int n = _args.d_a0;
                     return f0(std::move(n));
                   },
                   [&](const typename expr::EAdd _args) -> T1 {
                     std::shared_ptr<expr> e0 = _args.d_a0;
                     std::shared_ptr<expr> e1 = _args.d_a1;
                     return f1(e0, expr_rec<T1>(f, f0, f1, f2, f3, e0), e1,
                               expr_rec<T1>(f, f0, f1, f2, f3, e1));
                   },
                   [&](const typename expr::EMul _args) -> T1 {
                     std::shared_ptr<expr> e0 = _args.d_a0;
                     std::shared_ptr<expr> e1 = _args.d_a1;
                     return f2(e0, expr_rec<T1>(f, f0, f1, f2, f3, e0), e1,
                               expr_rec<T1>(f, f0, f1, f2, f3, e1));
                   },
                   [&](const typename expr::ECond _args) -> T1 {
                     std::shared_ptr<bexpr> b = _args.d_a0;
                     std::shared_ptr<expr> e0 = _args.d_a1;
                     std::shared_ptr<expr> e1 = _args.d_a2;
                     return f3(std::move(b), e0,
                               expr_rec<T1>(f, f0, f1, f2, f3, e0), e1,
                               expr_rec<T1>(f, f0, f1, f2, f3, e1));
                   }},
        e->v());
  }

  template <
      typename T1, MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F2,
      MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F3,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F4,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F5,
      MapsTo<T1, std::shared_ptr<bexpr>, T1> F6>
  static T1 bexpr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                       F5 &&f4, F6 &&f5, const std::shared_ptr<bexpr> &b) {
    return std::visit(
        Overloaded{
            [&](const typename bexpr::BTrue _args) -> T1 { return f; },
            [&](const typename bexpr::BFalse _args) -> T1 { return f0; },
            [&](const typename bexpr::BEq _args) -> T1 {
              std::shared_ptr<expr> e = _args.d_a0;
              std::shared_ptr<expr> e0 = _args.d_a1;
              return f1(std::move(e), std::move(e0));
            },
            [&](const typename bexpr::BLt _args) -> T1 {
              std::shared_ptr<expr> e = _args.d_a0;
              std::shared_ptr<expr> e0 = _args.d_a1;
              return f2(std::move(e), std::move(e0));
            },
            [&](const typename bexpr::BAnd _args) -> T1 {
              std::shared_ptr<bexpr> b0 = _args.d_a0;
              std::shared_ptr<bexpr> b1 = _args.d_a1;
              return f3(b0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, b0), b1,
                        bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, b1));
            },
            [&](const typename bexpr::BOr _args) -> T1 {
              std::shared_ptr<bexpr> b0 = _args.d_a0;
              std::shared_ptr<bexpr> b1 = _args.d_a1;
              return f4(b0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, b0), b1,
                        bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, b1));
            },
            [&](const typename bexpr::BNot _args) -> T1 {
              std::shared_ptr<bexpr> b0 = _args.d_a0;
              return f5(b0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, b0));
            }},
        b->v());
  }

  template <
      typename T1, MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F2,
      MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F3,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F4,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F5,
      MapsTo<T1, std::shared_ptr<bexpr>, T1> F6>
  static T1 bexpr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      F5 &&f4, F6 &&f5, const std::shared_ptr<bexpr> &b) {
    return std::visit(
        Overloaded{
            [&](const typename bexpr::BTrue _args) -> T1 { return f; },
            [&](const typename bexpr::BFalse _args) -> T1 { return f0; },
            [&](const typename bexpr::BEq _args) -> T1 {
              std::shared_ptr<expr> e = _args.d_a0;
              std::shared_ptr<expr> e0 = _args.d_a1;
              return f1(std::move(e), std::move(e0));
            },
            [&](const typename bexpr::BLt _args) -> T1 {
              std::shared_ptr<expr> e = _args.d_a0;
              std::shared_ptr<expr> e0 = _args.d_a1;
              return f2(std::move(e), std::move(e0));
            },
            [&](const typename bexpr::BAnd _args) -> T1 {
              std::shared_ptr<bexpr> b0 = _args.d_a0;
              std::shared_ptr<bexpr> b1 = _args.d_a1;
              return f3(b0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, b0), b1,
                        bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, b1));
            },
            [&](const typename bexpr::BOr _args) -> T1 {
              std::shared_ptr<bexpr> b0 = _args.d_a0;
              std::shared_ptr<bexpr> b1 = _args.d_a1;
              return f4(b0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, b0), b1,
                        bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, b1));
            },
            [&](const typename bexpr::BNot _args) -> T1 {
              std::shared_ptr<bexpr> b0 = _args.d_a0;
              return f5(b0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, b0));
            }},
        b->v());
  }

  __attribute__((pure)) static unsigned int
  expr_size(const std::shared_ptr<expr> &e);
  __attribute__((pure)) static unsigned int
  bexpr_size(const std::shared_ptr<bexpr> &b);
  __attribute__((pure)) static unsigned int
  stmt_size(const std::shared_ptr<stmt> &s);
  static inline const std::shared_ptr<expr> test_expr = expr::ctor::EAdd_(
      expr::ctor::ENum_(1u),
      expr::ctor::EMul_(expr::ctor::ENum_(2u), expr::ctor::ENum_(3u)));
  static inline const std::shared_ptr<bexpr> test_bexpr = bexpr::ctor::BAnd_(
      bexpr::ctor::BEq_(expr::ctor::EVar_(0u), expr::ctor::ENum_(5u)),
      bexpr::ctor::BLt_(expr::ctor::EVar_(1u), expr::ctor::ENum_(10u)));
  static inline const std::shared_ptr<stmt> test_stmt = stmt::ctor::SSeq_(
      stmt::ctor::SAssign_(0u, expr::ctor::ENum_(42u)),
      stmt::ctor::SIf_(
          bexpr::ctor::BEq_(expr::ctor::EVar_(0u), expr::ctor::ENum_(42u)),
          stmt::ctor::SSkip_(),
          stmt::ctor::SAssign_(0u, expr::ctor::ENum_(0u))));
  static inline const unsigned int test_expr_size = expr_size(test_expr);
  static inline const unsigned int test_bexpr_size = bexpr_size(test_bexpr);
  static inline const unsigned int test_stmt_size = stmt_size(test_stmt);
};

#endif // INCLUDED_LARGE_MUTUAL
