#ifndef INCLUDED_LARGE_MUTUAL
#define INCLUDED_LARGE_MUTUAL

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

  public:
    // CREATORS
    explicit stmt(SAssign _v) : d_v_(std::move(_v)) {}

    explicit stmt(SSeq _v) : d_v_(std::move(_v)) {}

    explicit stmt(SIf _v) : d_v_(std::move(_v)) {}

    explicit stmt(SWhile _v) : d_v_(std::move(_v)) {}

    explicit stmt(SSkip _v) : d_v_(_v) {}

    static std::shared_ptr<stmt> sassign(unsigned int a0,
                                         const std::shared_ptr<expr> &a1) {
      return std::make_shared<stmt>(SAssign{std::move(a0), a1});
    }

    static std::shared_ptr<stmt> sassign(unsigned int a0,
                                         std::shared_ptr<expr> &&a1) {
      return std::make_shared<stmt>(SAssign{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<stmt> sseq(const std::shared_ptr<stmt> &a0,
                                      const std::shared_ptr<stmt> &a1) {
      return std::make_shared<stmt>(SSeq{a0, a1});
    }

    static std::shared_ptr<stmt> sseq(std::shared_ptr<stmt> &&a0,
                                      std::shared_ptr<stmt> &&a1) {
      return std::make_shared<stmt>(SSeq{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<stmt> sif(const std::shared_ptr<bexpr> &a0,
                                     const std::shared_ptr<stmt> &a1,
                                     const std::shared_ptr<stmt> &a2) {
      return std::make_shared<stmt>(SIf{a0, a1, a2});
    }

    static std::shared_ptr<stmt> sif(std::shared_ptr<bexpr> &&a0,
                                     std::shared_ptr<stmt> &&a1,
                                     std::shared_ptr<stmt> &&a2) {
      return std::make_shared<stmt>(
          SIf{std::move(a0), std::move(a1), std::move(a2)});
    }

    static std::shared_ptr<stmt> swhile(const std::shared_ptr<bexpr> &a0,
                                        const std::shared_ptr<stmt> &a1) {
      return std::make_shared<stmt>(SWhile{a0, a1});
    }

    static std::shared_ptr<stmt> swhile(std::shared_ptr<bexpr> &&a0,
                                        std::shared_ptr<stmt> &&a1) {
      return std::make_shared<stmt>(SWhile{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<stmt> sskip() {
      return std::make_shared<stmt>(SSkip{});
    }

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

  public:
    // CREATORS
    explicit expr(ENum _v) : d_v_(std::move(_v)) {}

    explicit expr(EVar _v) : d_v_(std::move(_v)) {}

    explicit expr(EAdd _v) : d_v_(std::move(_v)) {}

    explicit expr(EMul _v) : d_v_(std::move(_v)) {}

    explicit expr(ECond _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<expr> ENum_(unsigned int a0) {
      return std::make_shared<expr>(ENum{std::move(a0)});
    }

    static std::shared_ptr<expr> evar(unsigned int a0) {
      return std::make_shared<expr>(EVar{std::move(a0)});
    }

    static std::shared_ptr<expr> eadd(const std::shared_ptr<expr> &a0,
                                      const std::shared_ptr<expr> &a1) {
      return std::make_shared<expr>(EAdd{a0, a1});
    }

    static std::shared_ptr<expr> eadd(std::shared_ptr<expr> &&a0,
                                      std::shared_ptr<expr> &&a1) {
      return std::make_shared<expr>(EAdd{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<expr> emul(const std::shared_ptr<expr> &a0,
                                      const std::shared_ptr<expr> &a1) {
      return std::make_shared<expr>(EMul{a0, a1});
    }

    static std::shared_ptr<expr> emul(std::shared_ptr<expr> &&a0,
                                      std::shared_ptr<expr> &&a1) {
      return std::make_shared<expr>(EMul{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<expr> econd(const std::shared_ptr<bexpr> &a0,
                                       const std::shared_ptr<expr> &a1,
                                       const std::shared_ptr<expr> &a2) {
      return std::make_shared<expr>(ECond{a0, a1, a2});
    }

    static std::shared_ptr<expr> econd(std::shared_ptr<bexpr> &&a0,
                                       std::shared_ptr<expr> &&a1,
                                       std::shared_ptr<expr> &&a2) {
      return std::make_shared<expr>(
          ECond{std::move(a0), std::move(a1), std::move(a2)});
    }

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

  public:
    // CREATORS
    explicit bexpr(BTrue _v) : d_v_(_v) {}

    explicit bexpr(BFalse _v) : d_v_(_v) {}

    explicit bexpr(BEq _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BLt _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BOr _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BNot _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<bexpr> btrue() {
      return std::make_shared<bexpr>(BTrue{});
    }

    static std::shared_ptr<bexpr> bfalse() {
      return std::make_shared<bexpr>(BFalse{});
    }

    static std::shared_ptr<bexpr> beq(const std::shared_ptr<expr> &a0,
                                      const std::shared_ptr<expr> &a1) {
      return std::make_shared<bexpr>(BEq{a0, a1});
    }

    static std::shared_ptr<bexpr> beq(std::shared_ptr<expr> &&a0,
                                      std::shared_ptr<expr> &&a1) {
      return std::make_shared<bexpr>(BEq{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<bexpr> blt(const std::shared_ptr<expr> &a0,
                                      const std::shared_ptr<expr> &a1) {
      return std::make_shared<bexpr>(BLt{a0, a1});
    }

    static std::shared_ptr<bexpr> blt(std::shared_ptr<expr> &&a0,
                                      std::shared_ptr<expr> &&a1) {
      return std::make_shared<bexpr>(BLt{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<bexpr> band(const std::shared_ptr<bexpr> &a0,
                                       const std::shared_ptr<bexpr> &a1) {
      return std::make_shared<bexpr>(BAnd{a0, a1});
    }

    static std::shared_ptr<bexpr> band(std::shared_ptr<bexpr> &&a0,
                                       std::shared_ptr<bexpr> &&a1) {
      return std::make_shared<bexpr>(BAnd{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<bexpr> bor(const std::shared_ptr<bexpr> &a0,
                                      const std::shared_ptr<bexpr> &a1) {
      return std::make_shared<bexpr>(BOr{a0, a1});
    }

    static std::shared_ptr<bexpr> bor(std::shared_ptr<bexpr> &&a0,
                                      std::shared_ptr<bexpr> &&a1) {
      return std::make_shared<bexpr>(BOr{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<bexpr> bnot(const std::shared_ptr<bexpr> &a0) {
      return std::make_shared<bexpr>(BNot{a0});
    }

    static std::shared_ptr<bexpr> bnot(std::shared_ptr<bexpr> &&a0) {
      return std::make_shared<bexpr>(BNot{std::move(a0)});
    }

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
    if (std::holds_alternative<typename stmt::SAssign>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SAssign>(&s->v());
      return f(_m.d_a0, _m.d_a1);
    } else if (std::holds_alternative<typename stmt::SSeq>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SSeq>(&s->v());
      return f0(_m.d_a0, stmt_rect<T1>(f, f0, f1, f2, f3, _m.d_a0), _m.d_a1,
                stmt_rect<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else if (std::holds_alternative<typename stmt::SIf>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SIf>(&s->v());
      return f1(_m.d_a0, _m.d_a1, stmt_rect<T1>(f, f0, f1, f2, f3, _m.d_a1),
                _m.d_a2, stmt_rect<T1>(f, f0, f1, f2, f3, _m.d_a2));
    } else if (std::holds_alternative<typename stmt::SWhile>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SWhile>(&s->v());
      return f2(_m.d_a0, _m.d_a1, stmt_rect<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else {
      return f3;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, std::shared_ptr<expr>> F0,
            MapsTo<T1, std::shared_ptr<stmt>, T1, std::shared_ptr<stmt>, T1> F1,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<stmt>, T1,
                   std::shared_ptr<stmt>, T1>
                F2,
            MapsTo<T1, std::shared_ptr<bexpr>, std::shared_ptr<stmt>, T1> F3>
  static T1 stmt_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, const T1 f3,
                     const std::shared_ptr<stmt> &s) {
    if (std::holds_alternative<typename stmt::SAssign>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SAssign>(&s->v());
      return f(_m.d_a0, _m.d_a1);
    } else if (std::holds_alternative<typename stmt::SSeq>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SSeq>(&s->v());
      return f0(_m.d_a0, stmt_rec<T1>(f, f0, f1, f2, f3, _m.d_a0), _m.d_a1,
                stmt_rec<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else if (std::holds_alternative<typename stmt::SIf>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SIf>(&s->v());
      return f1(_m.d_a0, _m.d_a1, stmt_rec<T1>(f, f0, f1, f2, f3, _m.d_a1),
                _m.d_a2, stmt_rec<T1>(f, f0, f1, f2, f3, _m.d_a2));
    } else if (std::holds_alternative<typename stmt::SWhile>(s->v())) {
      const auto &_m = *std::get_if<typename stmt::SWhile>(&s->v());
      return f2(_m.d_a0, _m.d_a1, stmt_rec<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else {
      return f3;
    }
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
    if (std::holds_alternative<typename expr::ENum>(e->v())) {
      const auto &_m = *std::get_if<typename expr::ENum>(&e->v());
      return f(_m.d_a0);
    } else if (std::holds_alternative<typename expr::EVar>(e->v())) {
      const auto &_m = *std::get_if<typename expr::EVar>(&e->v());
      return f0(_m.d_a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e->v())) {
      const auto &_m = *std::get_if<typename expr::EAdd>(&e->v());
      return f1(_m.d_a0, expr_rect<T1>(f, f0, f1, f2, f3, _m.d_a0), _m.d_a1,
                expr_rect<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else if (std::holds_alternative<typename expr::EMul>(e->v())) {
      const auto &_m = *std::get_if<typename expr::EMul>(&e->v());
      return f2(_m.d_a0, expr_rect<T1>(f, f0, f1, f2, f3, _m.d_a0), _m.d_a1,
                expr_rect<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else {
      const auto &_m = *std::get_if<typename expr::ECond>(&e->v());
      return f3(_m.d_a0, _m.d_a1, expr_rect<T1>(f, f0, f1, f2, f3, _m.d_a1),
                _m.d_a2, expr_rect<T1>(f, f0, f1, f2, f3, _m.d_a2));
    }
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
    if (std::holds_alternative<typename expr::ENum>(e->v())) {
      const auto &_m = *std::get_if<typename expr::ENum>(&e->v());
      return f(_m.d_a0);
    } else if (std::holds_alternative<typename expr::EVar>(e->v())) {
      const auto &_m = *std::get_if<typename expr::EVar>(&e->v());
      return f0(_m.d_a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e->v())) {
      const auto &_m = *std::get_if<typename expr::EAdd>(&e->v());
      return f1(_m.d_a0, expr_rec<T1>(f, f0, f1, f2, f3, _m.d_a0), _m.d_a1,
                expr_rec<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else if (std::holds_alternative<typename expr::EMul>(e->v())) {
      const auto &_m = *std::get_if<typename expr::EMul>(&e->v());
      return f2(_m.d_a0, expr_rec<T1>(f, f0, f1, f2, f3, _m.d_a0), _m.d_a1,
                expr_rec<T1>(f, f0, f1, f2, f3, _m.d_a1));
    } else {
      const auto &_m = *std::get_if<typename expr::ECond>(&e->v());
      return f3(_m.d_a0, _m.d_a1, expr_rec<T1>(f, f0, f1, f2, f3, _m.d_a1),
                _m.d_a2, expr_rec<T1>(f, f0, f1, f2, f3, _m.d_a2));
    }
  }

  template <
      typename T1, MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F2,
      MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F3,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F4,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F5,
      MapsTo<T1, std::shared_ptr<bexpr>, T1> F6>
  static T1 bexpr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                       F5 &&f4, F6 &&f5, const std::shared_ptr<bexpr> &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b->v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b->v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BEq>(&b->v());
      return f1(_m.d_a0, _m.d_a1);
    } else if (std::holds_alternative<typename bexpr::BLt>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BLt>(&b->v());
      return f2(_m.d_a0, _m.d_a1);
    } else if (std::holds_alternative<typename bexpr::BAnd>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BAnd>(&b->v());
      return f3(_m.d_a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a0),
                _m.d_a1, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a1));
    } else if (std::holds_alternative<typename bexpr::BOr>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BOr>(&b->v());
      return f4(_m.d_a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a0),
                _m.d_a1, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a1));
    } else {
      const auto &_m = *std::get_if<typename bexpr::BNot>(&b->v());
      return f5(_m.d_a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a0));
    }
  }

  template <
      typename T1, MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F2,
      MapsTo<T1, std::shared_ptr<expr>, std::shared_ptr<expr>> F3,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F4,
      MapsTo<T1, std::shared_ptr<bexpr>, T1, std::shared_ptr<bexpr>, T1> F5,
      MapsTo<T1, std::shared_ptr<bexpr>, T1> F6>
  static T1 bexpr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      F5 &&f4, F6 &&f5, const std::shared_ptr<bexpr> &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b->v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b->v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BEq>(&b->v());
      return f1(_m.d_a0, _m.d_a1);
    } else if (std::holds_alternative<typename bexpr::BLt>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BLt>(&b->v());
      return f2(_m.d_a0, _m.d_a1);
    } else if (std::holds_alternative<typename bexpr::BAnd>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BAnd>(&b->v());
      return f3(_m.d_a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a0),
                _m.d_a1, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a1));
    } else if (std::holds_alternative<typename bexpr::BOr>(b->v())) {
      const auto &_m = *std::get_if<typename bexpr::BOr>(&b->v());
      return f4(_m.d_a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a0),
                _m.d_a1, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a1));
    } else {
      const auto &_m = *std::get_if<typename bexpr::BNot>(&b->v());
      return f5(_m.d_a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, _m.d_a0));
    }
  }

  __attribute__((pure)) static unsigned int
  expr_size(const std::shared_ptr<expr> &e);
  __attribute__((pure)) static unsigned int
  bexpr_size(const std::shared_ptr<bexpr> &b);
  __attribute__((pure)) static unsigned int
  stmt_size(const std::shared_ptr<stmt> &s);
  static inline const std::shared_ptr<expr> test_expr =
      expr::eadd(expr::ENum_(1u), expr::emul(expr::ENum_(2u), expr::ENum_(3u)));
  static inline const std::shared_ptr<bexpr> test_bexpr =
      bexpr::band(bexpr::beq(expr::evar(0u), expr::ENum_(5u)),
                  bexpr::blt(expr::evar(1u), expr::ENum_(10u)));
  static inline const std::shared_ptr<stmt> test_stmt =
      stmt::sseq(stmt::sassign(0u, expr::ENum_(42u)),
                 stmt::sif(bexpr::beq(expr::evar(0u), expr::ENum_(42u)),
                           stmt::sskip(), stmt::sassign(0u, expr::ENum_(0u))));
  static inline const unsigned int test_expr_size = expr_size(test_expr);
  static inline const unsigned int test_bexpr_size = bexpr_size(test_bexpr);
  static inline const unsigned int test_stmt_size = stmt_size(test_stmt);
};

#endif // INCLUDED_LARGE_MUTUAL
