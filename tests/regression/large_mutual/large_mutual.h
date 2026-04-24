#ifndef INCLUDED_LARGE_MUTUAL
#define INCLUDED_LARGE_MUTUAL

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct LargeMutual {
  struct stmt;
  struct expr;
  struct bexpr;

  struct stmt {
    // TYPES
    struct SAssign {
      unsigned int d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct SSeq {
      std::unique_ptr<stmt> d_a0;
      std::unique_ptr<stmt> d_a1;
    };

    struct SIf {
      std::unique_ptr<bexpr> d_a0;
      std::unique_ptr<stmt> d_a1;
      std::unique_ptr<stmt> d_a2;
    };

    struct SWhile {
      std::unique_ptr<bexpr> d_a0;
      std::unique_ptr<stmt> d_a1;
    };

    struct SSkip {};

    using variant_t = std::variant<SAssign, SSeq, SIf, SWhile, SSkip>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    stmt() {}

    explicit stmt(SAssign _v) : d_v_(std::move(_v)) {}

    explicit stmt(SSeq _v) : d_v_(std::move(_v)) {}

    explicit stmt(SIf _v) : d_v_(std::move(_v)) {}

    explicit stmt(SWhile _v) : d_v_(std::move(_v)) {}

    explicit stmt(SSkip _v) : d_v_(_v) {}

    stmt(const stmt &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    stmt(stmt &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) stmt &operator=(const stmt &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) stmt &operator=(stmt &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) stmt clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<SAssign>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<SAssign>(_sv.v());
        return stmt(SAssign{clone_as_value<unsigned int>(d_a0),
                            clone_as_value<std::unique_ptr<expr>>(d_a1)});
      } else if (std::holds_alternative<SSeq>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<SSeq>(_sv.v());
        return stmt(SSeq{clone_as_value<std::unique_ptr<stmt>>(d_a0),
                         clone_as_value<std::unique_ptr<stmt>>(d_a1)});
      } else if (std::holds_alternative<SIf>(_sv.v())) {
        const auto &[d_a0, d_a1, d_a2] = std::get<SIf>(_sv.v());
        return stmt(SIf{clone_as_value<std::unique_ptr<bexpr>>(d_a0),
                        clone_as_value<std::unique_ptr<stmt>>(d_a1),
                        clone_as_value<std::unique_ptr<stmt>>(d_a2)});
      } else if (std::holds_alternative<SWhile>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<SWhile>(_sv.v());
        return stmt(SWhile{clone_as_value<std::unique_ptr<bexpr>>(d_a0),
                           clone_as_value<std::unique_ptr<stmt>>(d_a1)});
      } else {
        return stmt(SSkip{});
      }
    }

    // CREATORS
    __attribute__((pure)) static stmt sassign(unsigned int a0, const expr &a1) {
      return stmt(SAssign{std::move(a0), std::make_unique<expr>(a1.clone())});
    }

    __attribute__((pure)) static stmt sseq(const stmt &a0, const stmt &a1) {
      return stmt(SSeq{std::make_unique<stmt>(a0.clone()),
                       std::make_unique<stmt>(a1.clone())});
    }

    __attribute__((pure)) static stmt sif(const bexpr &a0, const stmt &a1,
                                          const stmt &a2) {
      return stmt(SIf{std::make_unique<bexpr>(a0.clone()),
                      std::make_unique<stmt>(a1.clone()),
                      std::make_unique<stmt>(a2.clone())});
    }

    __attribute__((pure)) static stmt swhile(const bexpr &a0, const stmt &a1) {
      return stmt(SWhile{std::make_unique<bexpr>(a0.clone()),
                         std::make_unique<stmt>(a1.clone())});
    }

    __attribute__((pure)) static stmt sskip() { return stmt(SSkip{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) stmt *operator->() { return this; }

    __attribute__((pure)) const stmt *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = stmt(); }

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
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct EMul {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct ECond {
      std::unique_ptr<bexpr> d_a0;
      std::unique_ptr<expr> d_a1;
      std::unique_ptr<expr> d_a2;
    };

    using variant_t = std::variant<ENum, EVar, EAdd, EMul, ECond>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(ENum _v) : d_v_(std::move(_v)) {}

    explicit expr(EVar _v) : d_v_(std::move(_v)) {}

    explicit expr(EAdd _v) : d_v_(std::move(_v)) {}

    explicit expr(EMul _v) : d_v_(std::move(_v)) {}

    explicit expr(ECond _v) : d_v_(std::move(_v)) {}

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
      if (std::holds_alternative<ENum>(_sv.v())) {
        const auto &[d_a0] = std::get<ENum>(_sv.v());
        return expr(ENum{clone_as_value<unsigned int>(d_a0)});
      } else if (std::holds_alternative<EVar>(_sv.v())) {
        const auto &[d_a0] = std::get<EVar>(_sv.v());
        return expr(EVar{clone_as_value<unsigned int>(d_a0)});
      } else if (std::holds_alternative<EAdd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<EAdd>(_sv.v());
        return expr(EAdd{clone_as_value<std::unique_ptr<expr>>(d_a0),
                         clone_as_value<std::unique_ptr<expr>>(d_a1)});
      } else if (std::holds_alternative<EMul>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<EMul>(_sv.v());
        return expr(EMul{clone_as_value<std::unique_ptr<expr>>(d_a0),
                         clone_as_value<std::unique_ptr<expr>>(d_a1)});
      } else {
        const auto &[d_a0, d_a1, d_a2] = std::get<ECond>(_sv.v());
        return expr(ECond{clone_as_value<std::unique_ptr<bexpr>>(d_a0),
                          clone_as_value<std::unique_ptr<expr>>(d_a1),
                          clone_as_value<std::unique_ptr<expr>>(d_a2)});
      }
    }

    // CREATORS
    __attribute__((pure)) static expr ENum_(unsigned int a0) {
      return expr(ENum{std::move(a0)});
    }

    __attribute__((pure)) static expr evar(unsigned int a0) {
      return expr(EVar{std::move(a0)});
    }

    __attribute__((pure)) static expr eadd(const expr &a0, const expr &a1) {
      return expr(EAdd{std::make_unique<expr>(a0.clone()),
                       std::make_unique<expr>(a1.clone())});
    }

    __attribute__((pure)) static expr emul(const expr &a0, const expr &a1) {
      return expr(EMul{std::make_unique<expr>(a0.clone()),
                       std::make_unique<expr>(a1.clone())});
    }

    __attribute__((pure)) static expr econd(const bexpr &a0, const expr &a1,
                                            const expr &a2) {
      return expr(ECond{std::make_unique<bexpr>(a0.clone()),
                        std::make_unique<expr>(a1.clone()),
                        std::make_unique<expr>(a2.clone())});
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
  };

  struct bexpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BEq {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct BLt {
      std::unique_ptr<expr> d_a0;
      std::unique_ptr<expr> d_a1;
    };

    struct BAnd {
      std::unique_ptr<bexpr> d_a0;
      std::unique_ptr<bexpr> d_a1;
    };

    struct BOr {
      std::unique_ptr<bexpr> d_a0;
      std::unique_ptr<bexpr> d_a1;
    };

    struct BNot {
      std::unique_ptr<bexpr> d_a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BEq, BLt, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    bexpr() {}

    explicit bexpr(BTrue _v) : d_v_(_v) {}

    explicit bexpr(BFalse _v) : d_v_(_v) {}

    explicit bexpr(BEq _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BLt _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BAnd _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BOr _v) : d_v_(std::move(_v)) {}

    explicit bexpr(BNot _v) : d_v_(std::move(_v)) {}

    bexpr(const bexpr &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    bexpr(bexpr &&_other) : d_v_(std::move(_other.d_v_)) {}

    __attribute__((pure)) bexpr &operator=(const bexpr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    __attribute__((pure)) bexpr &operator=(bexpr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) bexpr clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<BTrue>(_sv.v())) {
        return bexpr(BTrue{});
      } else if (std::holds_alternative<BFalse>(_sv.v())) {
        return bexpr(BFalse{});
      } else if (std::holds_alternative<BEq>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BEq>(_sv.v());
        return bexpr(BEq{clone_as_value<std::unique_ptr<expr>>(d_a0),
                         clone_as_value<std::unique_ptr<expr>>(d_a1)});
      } else if (std::holds_alternative<BLt>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BLt>(_sv.v());
        return bexpr(BLt{clone_as_value<std::unique_ptr<expr>>(d_a0),
                         clone_as_value<std::unique_ptr<expr>>(d_a1)});
      } else if (std::holds_alternative<BAnd>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BAnd>(_sv.v());
        return bexpr(BAnd{clone_as_value<std::unique_ptr<bexpr>>(d_a0),
                          clone_as_value<std::unique_ptr<bexpr>>(d_a1)});
      } else if (std::holds_alternative<BOr>(_sv.v())) {
        const auto &[d_a0, d_a1] = std::get<BOr>(_sv.v());
        return bexpr(BOr{clone_as_value<std::unique_ptr<bexpr>>(d_a0),
                         clone_as_value<std::unique_ptr<bexpr>>(d_a1)});
      } else {
        const auto &[d_a0] = std::get<BNot>(_sv.v());
        return bexpr(BNot{clone_as_value<std::unique_ptr<bexpr>>(d_a0)});
      }
    }

    // CREATORS
    __attribute__((pure)) static bexpr btrue() { return bexpr(BTrue{}); }

    __attribute__((pure)) static bexpr bfalse() { return bexpr(BFalse{}); }

    __attribute__((pure)) static bexpr beq(const expr &a0, const expr &a1) {
      return bexpr(BEq{std::make_unique<expr>(a0.clone()),
                       std::make_unique<expr>(a1.clone())});
    }

    __attribute__((pure)) static bexpr blt(const expr &a0, const expr &a1) {
      return bexpr(BLt{std::make_unique<expr>(a0.clone()),
                       std::make_unique<expr>(a1.clone())});
    }

    __attribute__((pure)) static bexpr band(const bexpr &a0, const bexpr &a1) {
      return bexpr(BAnd{std::make_unique<bexpr>(a0.clone()),
                        std::make_unique<bexpr>(a1.clone())});
    }

    __attribute__((pure)) static bexpr bor(const bexpr &a0, const bexpr &a1) {
      return bexpr(BOr{std::make_unique<bexpr>(a0.clone()),
                       std::make_unique<bexpr>(a1.clone())});
    }

    __attribute__((pure)) static bexpr bnot(const bexpr &a0) {
      return bexpr(BNot{std::make_unique<bexpr>(a0.clone())});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) bexpr *operator->() { return this; }

    __attribute__((pure)) const bexpr *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = bexpr(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int, expr> F0,
            MapsTo<T1, stmt, T1, stmt, T1> F1,
            MapsTo<T1, bexpr, stmt, T1, stmt, T1> F2,
            MapsTo<T1, bexpr, stmt, T1> F3>
  static T1 stmt_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, const T1 f3,
                      const stmt &s) {
    if (std::holds_alternative<typename stmt::SAssign>(s.v())) {
      const auto &[d_a0, d_a1] = std::get<typename stmt::SAssign>(s.v());
      return f(d_a0, *(d_a1));
    } else if (std::holds_alternative<typename stmt::SSeq>(s.v())) {
      const auto &[d_a0, d_a1] = std::get<typename stmt::SSeq>(s.v());
      return f0(*(d_a0), stmt_rect<T1>(f, f0, f1, f2, f3, *(d_a0)), *(d_a1),
                stmt_rect<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else if (std::holds_alternative<typename stmt::SIf>(s.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename stmt::SIf>(s.v());
      return f1(*(d_a0), *(d_a1), stmt_rect<T1>(f, f0, f1, f2, f3, *(d_a1)),
                *(d_a2), stmt_rect<T1>(f, f0, f1, f2, f3, *(d_a2)));
    } else if (std::holds_alternative<typename stmt::SWhile>(s.v())) {
      const auto &[d_a0, d_a1] = std::get<typename stmt::SWhile>(s.v());
      return f2(*(d_a0), *(d_a1), stmt_rect<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else {
      return f3;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int, expr> F0,
            MapsTo<T1, stmt, T1, stmt, T1> F1,
            MapsTo<T1, bexpr, stmt, T1, stmt, T1> F2,
            MapsTo<T1, bexpr, stmt, T1> F3>
  static T1 stmt_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, const T1 f3,
                     const stmt &s) {
    if (std::holds_alternative<typename stmt::SAssign>(s.v())) {
      const auto &[d_a0, d_a1] = std::get<typename stmt::SAssign>(s.v());
      return f(d_a0, *(d_a1));
    } else if (std::holds_alternative<typename stmt::SSeq>(s.v())) {
      const auto &[d_a0, d_a1] = std::get<typename stmt::SSeq>(s.v());
      return f0(*(d_a0), stmt_rec<T1>(f, f0, f1, f2, f3, *(d_a0)), *(d_a1),
                stmt_rec<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else if (std::holds_alternative<typename stmt::SIf>(s.v())) {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename stmt::SIf>(s.v());
      return f1(*(d_a0), *(d_a1), stmt_rec<T1>(f, f0, f1, f2, f3, *(d_a1)),
                *(d_a2), stmt_rec<T1>(f, f0, f1, f2, f3, *(d_a2)));
    } else if (std::holds_alternative<typename stmt::SWhile>(s.v())) {
      const auto &[d_a0, d_a1] = std::get<typename stmt::SWhile>(s.v());
      return f2(*(d_a0), *(d_a1), stmt_rec<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else {
      return f3;
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, expr, T1, expr, T1> F2,
            MapsTo<T1, expr, T1, expr, T1> F3,
            MapsTo<T1, bexpr, expr, T1, expr, T1> F4>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const expr &e) {
    if (std::holds_alternative<typename expr::ENum>(e.v())) {
      const auto &[d_a0] = std::get<typename expr::ENum>(e.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename expr::EVar>(e.v())) {
      const auto &[d_a0] = std::get<typename expr::EVar>(e.v());
      return f0(d_a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e.v())) {
      const auto &[d_a0, d_a1] = std::get<typename expr::EAdd>(e.v());
      return f1(*(d_a0), expr_rect<T1>(f, f0, f1, f2, f3, *(d_a0)), *(d_a1),
                expr_rect<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else if (std::holds_alternative<typename expr::EMul>(e.v())) {
      const auto &[d_a0, d_a1] = std::get<typename expr::EMul>(e.v());
      return f2(*(d_a0), expr_rect<T1>(f, f0, f1, f2, f3, *(d_a0)), *(d_a1),
                expr_rect<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::ECond>(e.v());
      return f3(*(d_a0), *(d_a1), expr_rect<T1>(f, f0, f1, f2, f3, *(d_a1)),
                *(d_a2), expr_rect<T1>(f, f0, f1, f2, f3, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, unsigned int> F1, MapsTo<T1, expr, T1, expr, T1> F2,
            MapsTo<T1, expr, T1, expr, T1> F3,
            MapsTo<T1, bexpr, expr, T1, expr, T1> F4>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                     const expr &e) {
    if (std::holds_alternative<typename expr::ENum>(e.v())) {
      const auto &[d_a0] = std::get<typename expr::ENum>(e.v());
      return f(d_a0);
    } else if (std::holds_alternative<typename expr::EVar>(e.v())) {
      const auto &[d_a0] = std::get<typename expr::EVar>(e.v());
      return f0(d_a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e.v())) {
      const auto &[d_a0, d_a1] = std::get<typename expr::EAdd>(e.v());
      return f1(*(d_a0), expr_rec<T1>(f, f0, f1, f2, f3, *(d_a0)), *(d_a1),
                expr_rec<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else if (std::holds_alternative<typename expr::EMul>(e.v())) {
      const auto &[d_a0, d_a1] = std::get<typename expr::EMul>(e.v());
      return f2(*(d_a0), expr_rec<T1>(f, f0, f1, f2, f3, *(d_a0)), *(d_a1),
                expr_rec<T1>(f, f0, f1, f2, f3, *(d_a1)));
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename expr::ECond>(e.v());
      return f3(*(d_a0), *(d_a1), expr_rec<T1>(f, f0, f1, f2, f3, *(d_a1)),
                *(d_a2), expr_rec<T1>(f, f0, f1, f2, f3, *(d_a2)));
    }
  }

  template <typename T1, MapsTo<T1, expr, expr> F2, MapsTo<T1, expr, expr> F3,
            MapsTo<T1, bexpr, T1, bexpr, T1> F4,
            MapsTo<T1, bexpr, T1, bexpr, T1> F5, MapsTo<T1, bexpr, T1> F6>
  static T1 bexpr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                       F5 &&f4, F6 &&f5, const bexpr &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b.v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BEq>(b.v());
      return f1(*(d_a0), *(d_a1));
    } else if (std::holds_alternative<typename bexpr::BLt>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BLt>(b.v());
      return f2(*(d_a0), *(d_a1));
    } else if (std::holds_alternative<typename bexpr::BAnd>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BAnd>(b.v());
      return f3(*(d_a0), bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a0)),
                *(d_a1), bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a1)));
    } else if (std::holds_alternative<typename bexpr::BOr>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BOr>(b.v());
      return f4(*(d_a0), bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a0)),
                *(d_a1), bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a1)));
    } else {
      const auto &[d_a0] = std::get<typename bexpr::BNot>(b.v());
      return f5(*(d_a0), bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a0)));
    }
  }

  template <typename T1, MapsTo<T1, expr, expr> F2, MapsTo<T1, expr, expr> F3,
            MapsTo<T1, bexpr, T1, bexpr, T1> F4,
            MapsTo<T1, bexpr, T1, bexpr, T1> F5, MapsTo<T1, bexpr, T1> F6>
  static T1 bexpr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      F5 &&f4, F6 &&f5, const bexpr &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b.v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BEq>(b.v());
      return f1(*(d_a0), *(d_a1));
    } else if (std::holds_alternative<typename bexpr::BLt>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BLt>(b.v());
      return f2(*(d_a0), *(d_a1));
    } else if (std::holds_alternative<typename bexpr::BAnd>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BAnd>(b.v());
      return f3(*(d_a0), bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a0)),
                *(d_a1), bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a1)));
    } else if (std::holds_alternative<typename bexpr::BOr>(b.v())) {
      const auto &[d_a0, d_a1] = std::get<typename bexpr::BOr>(b.v());
      return f4(*(d_a0), bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a0)),
                *(d_a1), bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a1)));
    } else {
      const auto &[d_a0] = std::get<typename bexpr::BNot>(b.v());
      return f5(*(d_a0), bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_a0)));
    }
  }

  __attribute__((pure)) static unsigned int expr_size(const expr &e);
  __attribute__((pure)) static unsigned int bexpr_size(const bexpr &b);
  __attribute__((pure)) static unsigned int stmt_size(const stmt &s);
  static inline const expr test_expr =
      expr::eadd(expr::ENum_(1u), expr::emul(expr::ENum_(2u), expr::ENum_(3u)));
  static inline const bexpr test_bexpr =
      bexpr::band(bexpr::beq(expr::evar(0u), expr::ENum_(5u)),
                  bexpr::blt(expr::evar(1u), expr::ENum_(10u)));
  static inline const stmt test_stmt =
      stmt::sseq(stmt::sassign(0u, expr::ENum_(42u)),
                 stmt::sif(bexpr::beq(expr::evar(0u), expr::ENum_(42u)),
                           stmt::sskip(), stmt::sassign(0u, expr::ENum_(0u))));
  static inline const unsigned int test_expr_size = expr_size(test_expr);
  static inline const unsigned int test_bexpr_size = bexpr_size(test_bexpr);
  static inline const unsigned int test_stmt_size = stmt_size(test_stmt);
};

#endif // INCLUDED_LARGE_MUTUAL
