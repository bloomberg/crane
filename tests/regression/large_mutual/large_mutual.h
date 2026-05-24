#ifndef INCLUDED_LARGE_MUTUAL
#define INCLUDED_LARGE_MUTUAL

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct LargeMutual {
  struct stmt;
  struct expr;
  struct bexpr;

  struct stmt {
    // TYPES
    struct SAssign {
      uint64_t a0;
      std::shared_ptr<expr> a1;
    };

    struct SSeq {
      std::shared_ptr<stmt> a0;
      std::shared_ptr<stmt> a1;
    };

    struct SIf {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<stmt> a1;
      std::shared_ptr<stmt> a2;
    };

    struct SWhile {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<stmt> a1;
    };

    struct SSkip {};

    using variant_t = std::variant<SAssign, SSeq, SIf, SWhile, SSkip>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    stmt() {}

    explicit stmt(SAssign _v) : v_(std::move(_v)) {}

    explicit stmt(SSeq _v) : v_(std::move(_v)) {}

    explicit stmt(SIf _v) : v_(std::move(_v)) {}

    explicit stmt(SWhile _v) : v_(std::move(_v)) {}

    explicit stmt(SSkip _v) : v_(_v) {}

    stmt(const stmt &_other) : v_(std::move(_other.clone().v_)) {}

    stmt(stmt &&_other) noexcept : v_(std::move(_other.v_)) {}

    stmt &operator=(const stmt &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    stmt &operator=(stmt &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    stmt clone() const {
      stmt _out{};

      struct _CloneFrame {
        const stmt *_src;
        stmt *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const stmt *_src = _frame._src;
        stmt *_dst = _frame._dst;
        if (std::holds_alternative<SAssign>(_src->v())) {
          const auto &_alt = std::get<SAssign>(_src->v());
          _dst->v_ = SAssign{
              _alt.a0,
              _alt.a1 ? std::make_shared<LargeMutual::expr>(_alt.a1->clone())
                      : nullptr};
        } else if (std::holds_alternative<SSeq>(_src->v())) {
          const auto &_alt = std::get<SSeq>(_src->v());
          _dst->v_ = SSeq{_alt.a0 ? std::make_shared<stmt>() : nullptr,
                          _alt.a1 ? std::make_shared<stmt>() : nullptr};
          auto &_dst_alt = std::get<SSeq>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<SIf>(_src->v())) {
          const auto &_alt = std::get<SIf>(_src->v());
          _dst->v_ = SIf{
              _alt.a0 ? std::make_shared<LargeMutual::bexpr>(_alt.a0->clone())
                      : nullptr,
              _alt.a1 ? std::make_shared<stmt>() : nullptr,
              _alt.a2 ? std::make_shared<stmt>() : nullptr};
          auto &_dst_alt = std::get<SIf>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        } else if (std::holds_alternative<SWhile>(_src->v())) {
          const auto &_alt = std::get<SWhile>(_src->v());
          _dst->v_ = SWhile{
              _alt.a0 ? std::make_shared<LargeMutual::bexpr>(_alt.a0->clone())
                      : nullptr,
              _alt.a1 ? std::make_shared<stmt>() : nullptr};
          auto &_dst_alt = std::get<SWhile>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          _dst->v_ = SSkip{};
        }
      }
      return _out;
    }

    // CREATORS
    static stmt sassign(uint64_t a0, expr a1) {
      return stmt(SAssign{a0, std::make_shared<expr>(std::move(a1))});
    }

    static stmt sseq(stmt a0, stmt a1) {
      return stmt(SSeq{std::make_shared<stmt>(std::move(a0)),
                       std::make_shared<stmt>(std::move(a1))});
    }

    static stmt sif(bexpr a0, stmt a1, stmt a2) {
      return stmt(SIf{std::make_shared<bexpr>(std::move(a0)),
                      std::make_shared<stmt>(std::move(a1)),
                      std::make_shared<stmt>(std::move(a2))});
    }

    static stmt swhile(bexpr a0, stmt a1) {
      return stmt(SWhile{std::make_shared<bexpr>(std::move(a0)),
                         std::make_shared<stmt>(std::move(a1))});
    }

    static stmt sskip() { return stmt(SSkip{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct expr {
    // TYPES
    struct ENum {
      uint64_t a0;
    };

    struct EVar {
      uint64_t a0;
    };

    struct EAdd {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct EMul {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct ECond {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
    };

    using variant_t = std::variant<ENum, EVar, EAdd, EMul, ECond>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(ENum _v) : v_(std::move(_v)) {}

    explicit expr(EVar _v) : v_(std::move(_v)) {}

    explicit expr(EAdd _v) : v_(std::move(_v)) {}

    explicit expr(EMul _v) : v_(std::move(_v)) {}

    explicit expr(ECond _v) : v_(std::move(_v)) {}

    expr(const expr &_other) : v_(std::move(_other.clone().v_)) {}

    expr(expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    expr &operator=(const expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    expr &operator=(expr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    expr clone() const {
      expr _out{};

      struct _CloneFrame {
        const expr *_src;
        expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const expr *_src = _frame._src;
        expr *_dst = _frame._dst;
        if (std::holds_alternative<ENum>(_src->v())) {
          const auto &_alt = std::get<ENum>(_src->v());
          _dst->v_ = ENum{_alt.a0};
        } else if (std::holds_alternative<EVar>(_src->v())) {
          const auto &_alt = std::get<EVar>(_src->v());
          _dst->v_ = EVar{_alt.a0};
        } else if (std::holds_alternative<EAdd>(_src->v())) {
          const auto &_alt = std::get<EAdd>(_src->v());
          _dst->v_ = EAdd{_alt.a0 ? std::make_shared<expr>() : nullptr,
                          _alt.a1 ? std::make_shared<expr>() : nullptr};
          auto &_dst_alt = std::get<EAdd>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<EMul>(_src->v())) {
          const auto &_alt = std::get<EMul>(_src->v());
          _dst->v_ = EMul{_alt.a0 ? std::make_shared<expr>() : nullptr,
                          _alt.a1 ? std::make_shared<expr>() : nullptr};
          auto &_dst_alt = std::get<EMul>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<ECond>(_src->v());
          _dst->v_ = ECond{
              _alt.a0 ? std::make_shared<LargeMutual::bexpr>(_alt.a0->clone())
                      : nullptr,
              _alt.a1 ? std::make_shared<expr>() : nullptr,
              _alt.a2 ? std::make_shared<expr>() : nullptr};
          auto &_dst_alt = std::get<ECond>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static expr ENum_(uint64_t a0) { return expr(ENum{a0}); }

    static expr evar(uint64_t a0) { return expr(EVar{a0}); }

    static expr eadd(expr a0, expr a1) {
      return expr(EAdd{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static expr emul(expr a0, expr a1) {
      return expr(EMul{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static expr econd(bexpr a0, expr a1, expr a2) {
      return expr(ECond{std::make_shared<bexpr>(std::move(a0)),
                        std::make_shared<expr>(std::move(a1)),
                        std::make_shared<expr>(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  struct bexpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BEq {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct BLt {
      std::shared_ptr<expr> a0;
      std::shared_ptr<expr> a1;
    };

    struct BAnd {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<bexpr> a1;
    };

    struct BOr {
      std::shared_ptr<bexpr> a0;
      std::shared_ptr<bexpr> a1;
    };

    struct BNot {
      std::shared_ptr<bexpr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BEq, BLt, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bexpr() {}

    explicit bexpr(BTrue _v) : v_(_v) {}

    explicit bexpr(BFalse _v) : v_(_v) {}

    explicit bexpr(BEq _v) : v_(std::move(_v)) {}

    explicit bexpr(BLt _v) : v_(std::move(_v)) {}

    explicit bexpr(BAnd _v) : v_(std::move(_v)) {}

    explicit bexpr(BOr _v) : v_(std::move(_v)) {}

    explicit bexpr(BNot _v) : v_(std::move(_v)) {}

    bexpr(const bexpr &_other) : v_(std::move(_other.clone().v_)) {}

    bexpr(bexpr &&_other) noexcept : v_(std::move(_other.v_)) {}

    bexpr &operator=(const bexpr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    bexpr &operator=(bexpr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    bexpr clone() const {
      bexpr _out{};

      struct _CloneFrame {
        const bexpr *_src;
        bexpr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const bexpr *_src = _frame._src;
        bexpr *_dst = _frame._dst;
        if (std::holds_alternative<BTrue>(_src->v())) {
          _dst->v_ = BTrue{};
        } else if (std::holds_alternative<BFalse>(_src->v())) {
          _dst->v_ = BFalse{};
        } else if (std::holds_alternative<BEq>(_src->v())) {
          const auto &_alt = std::get<BEq>(_src->v());
          _dst->v_ = BEq{
              _alt.a0 ? std::make_shared<LargeMutual::expr>(_alt.a0->clone())
                      : nullptr,
              _alt.a1 ? std::make_shared<LargeMutual::expr>(_alt.a1->clone())
                      : nullptr};
        } else if (std::holds_alternative<BLt>(_src->v())) {
          const auto &_alt = std::get<BLt>(_src->v());
          _dst->v_ = BLt{
              _alt.a0 ? std::make_shared<LargeMutual::expr>(_alt.a0->clone())
                      : nullptr,
              _alt.a1 ? std::make_shared<LargeMutual::expr>(_alt.a1->clone())
                      : nullptr};
        } else if (std::holds_alternative<BAnd>(_src->v())) {
          const auto &_alt = std::get<BAnd>(_src->v());
          _dst->v_ = BAnd{_alt.a0 ? std::make_shared<bexpr>() : nullptr,
                          _alt.a1 ? std::make_shared<bexpr>() : nullptr};
          auto &_dst_alt = std::get<BAnd>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<BOr>(_src->v())) {
          const auto &_alt = std::get<BOr>(_src->v());
          _dst->v_ = BOr{_alt.a0 ? std::make_shared<bexpr>() : nullptr,
                         _alt.a1 ? std::make_shared<bexpr>() : nullptr};
          auto &_dst_alt = std::get<BOr>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<BNot>(_src->v());
          _dst->v_ = BNot{_alt.a0 ? std::make_shared<bexpr>() : nullptr};
          auto &_dst_alt = std::get<BNot>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static bexpr btrue() { return bexpr(BTrue{}); }

    static bexpr bfalse() { return bexpr(BFalse{}); }

    static bexpr beq(expr a0, expr a1) {
      return bexpr(BEq{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static bexpr blt(expr a0, expr a1) {
      return bexpr(BLt{std::make_shared<expr>(std::move(a0)),
                       std::make_shared<expr>(std::move(a1))});
    }

    static bexpr band(bexpr a0, bexpr a1) {
      return bexpr(BAnd{std::make_shared<bexpr>(std::move(a0)),
                        std::make_shared<bexpr>(std::move(a1))});
    }

    static bexpr bor(bexpr a0, bexpr a1) {
      return bexpr(BOr{std::make_shared<bexpr>(std::move(a0)),
                       std::make_shared<bexpr>(std::move(a1))});
    }

    static bexpr bnot(bexpr a0) {
      return bexpr(BNot{std::make_shared<bexpr>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, expr &> &&
             std::is_invocable_r_v<T1, F1 &, stmt &, T1 &, stmt &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, bexpr &, stmt &, T1 &, stmt &,
                                   T1 &> &&
             std::is_invocable_r_v<T1, F3 &, bexpr &, stmt &, T1 &>
  static T1 stmt_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, T1 f3, const stmt &s) {
    if (std::holds_alternative<typename stmt::SAssign>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SAssign>(s.v());
      return f(a0, *a1);
    } else if (std::holds_alternative<typename stmt::SSeq>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SSeq>(s.v());
      return f0(*a0, stmt_rect<T1>(f, f0, f1, f2, f3, *a0), *a1,
                stmt_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename stmt::SIf>(s.v())) {
      const auto &[a0, a1, a2] = std::get<typename stmt::SIf>(s.v());
      return f1(*a0, *a1, stmt_rect<T1>(f, f0, f1, f2, f3, *a1), *a2,
                stmt_rect<T1>(f, f0, f1, f2, f3, *a2));
    } else if (std::holds_alternative<typename stmt::SWhile>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SWhile>(s.v());
      return f2(*a0, *a1, stmt_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      return f3;
    }
  }

  template <typename T1, typename F0, typename F1, typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, expr &> &&
             std::is_invocable_r_v<T1, F1 &, stmt &, T1 &, stmt &, T1 &> &&
             std::is_invocable_r_v<T1, F2 &, bexpr &, stmt &, T1 &, stmt &,
                                   T1 &> &&
             std::is_invocable_r_v<T1, F3 &, bexpr &, stmt &, T1 &>
  static T1 stmt_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, T1 f3, const stmt &s) {
    if (std::holds_alternative<typename stmt::SAssign>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SAssign>(s.v());
      return f(a0, *a1);
    } else if (std::holds_alternative<typename stmt::SSeq>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SSeq>(s.v());
      return f0(*a0, stmt_rec<T1>(f, f0, f1, f2, f3, *a0), *a1,
                stmt_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename stmt::SIf>(s.v())) {
      const auto &[a0, a1, a2] = std::get<typename stmt::SIf>(s.v());
      return f1(*a0, *a1, stmt_rec<T1>(f, f0, f1, f2, f3, *a1), *a2,
                stmt_rec<T1>(f, f0, f1, f2, f3, *a2));
    } else if (std::holds_alternative<typename stmt::SWhile>(s.v())) {
      const auto &[a0, a1] = std::get<typename stmt::SWhile>(s.v());
      return f2(*a0, *a1, stmt_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      return f3;
    }
  }

  template <typename T1, typename F0, typename F1, typename F2, typename F3,
            typename F4>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, expr &, T1 &, expr &,
                                   T1 &>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const expr &e) {
    if (std::holds_alternative<typename expr::ENum>(e.v())) {
      const auto &[a0] = std::get<typename expr::ENum>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::EVar>(e.v())) {
      const auto &[a0] = std::get<typename expr::EVar>(e.v());
      return f0(a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EAdd>(e.v());
      return f1(*a0, expr_rect<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename expr::EMul>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EMul>(e.v());
      return f2(*a0, expr_rect<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rect<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      const auto &[a0, a1, a2] = std::get<typename expr::ECond>(e.v());
      return f3(*a0, *a1, expr_rect<T1>(f, f0, f1, f2, f3, *a1), *a2,
                expr_rect<T1>(f, f0, f1, f2, f3, *a2));
    }
  }

  template <typename T1, typename F0, typename F1, typename F2, typename F3,
            typename F4>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, T1 &, expr &, T1 &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, expr &, T1 &, expr &,
                                   T1 &>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3,
                     const expr &e) {
    if (std::holds_alternative<typename expr::ENum>(e.v())) {
      const auto &[a0] = std::get<typename expr::ENum>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::EVar>(e.v())) {
      const auto &[a0] = std::get<typename expr::EVar>(e.v());
      return f0(a0);
    } else if (std::holds_alternative<typename expr::EAdd>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EAdd>(e.v());
      return f1(*a0, expr_rec<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else if (std::holds_alternative<typename expr::EMul>(e.v())) {
      const auto &[a0, a1] = std::get<typename expr::EMul>(e.v());
      return f2(*a0, expr_rec<T1>(f, f0, f1, f2, f3, *a0), *a1,
                expr_rec<T1>(f, f0, f1, f2, f3, *a1));
    } else {
      const auto &[a0, a1, a2] = std::get<typename expr::ECond>(e.v());
      return f3(*a0, *a1, expr_rec<T1>(f, f0, f1, f2, f3, *a1), *a2,
                expr_rec<T1>(f, f0, f1, f2, f3, *a2));
    }
  }

  template <typename T1, typename F2, typename F3, typename F4, typename F5,
            typename F6>
    requires std::is_invocable_r_v<T1, F2 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F5 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F6 &, bexpr &, T1 &>
  static T1 bexpr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
                       const bexpr &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b.v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BEq>(b.v());
      return f1(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BLt>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BLt>(b.v());
      return f2(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BAnd>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BAnd>(b.v());
      return f3(*a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else if (std::holds_alternative<typename bexpr::BOr>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BOr>(b.v());
      return f4(*a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else {
      const auto &[a0] = std::get<typename bexpr::BNot>(b.v());
      return f5(*a0, bexpr_rect<T1>(f, f0, f1, f2, f3, f4, f5, *a0));
    }
  }

  template <typename T1, typename F2, typename F3, typename F4, typename F5,
            typename F6>
    requires std::is_invocable_r_v<T1, F2 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F3 &, expr &, expr &> &&
             std::is_invocable_r_v<T1, F4 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F5 &, bexpr &, T1 &, bexpr &, T1 &> &&
             std::is_invocable_r_v<T1, F6 &, bexpr &, T1 &>
  static T1 bexpr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4, F6 &&f5,
                      const bexpr &b) {
    if (std::holds_alternative<typename bexpr::BTrue>(b.v())) {
      return f;
    } else if (std::holds_alternative<typename bexpr::BFalse>(b.v())) {
      return f0;
    } else if (std::holds_alternative<typename bexpr::BEq>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BEq>(b.v());
      return f1(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BLt>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BLt>(b.v());
      return f2(*a0, *a1);
    } else if (std::holds_alternative<typename bexpr::BAnd>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BAnd>(b.v());
      return f3(*a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else if (std::holds_alternative<typename bexpr::BOr>(b.v())) {
      const auto &[a0, a1] = std::get<typename bexpr::BOr>(b.v());
      return f4(*a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a0), *a1,
                bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a1));
    } else {
      const auto &[a0] = std::get<typename bexpr::BNot>(b.v());
      return f5(*a0, bexpr_rec<T1>(f, f0, f1, f2, f3, f4, f5, *a0));
    }
  }

  static uint64_t expr_size(const expr &e);
  static uint64_t bexpr_size(const bexpr &b);
  static uint64_t stmt_size(const stmt &s);
  static inline const expr test_expr = expr::eadd(
      expr::ENum_(UINT64_C(1)),
      expr::emul(expr::ENum_(UINT64_C(2)), expr::ENum_(UINT64_C(3))));
  static inline const bexpr test_bexpr = bexpr::band(
      bexpr::beq(expr::evar(UINT64_C(0)), expr::ENum_(UINT64_C(5))),
      bexpr::blt(expr::evar(UINT64_C(1)), expr::ENum_(UINT64_C(10))));
  static inline const stmt test_stmt = stmt::sseq(
      stmt::sassign(UINT64_C(0), expr::ENum_(UINT64_C(42))),
      stmt::sif(bexpr::beq(expr::evar(UINT64_C(0)), expr::ENum_(UINT64_C(42))),
                stmt::sskip(),
                stmt::sassign(UINT64_C(0), expr::ENum_(UINT64_C(0)))));
  static inline const uint64_t test_expr_size = expr_size(test_expr);
  static inline const uint64_t test_bexpr_size = bexpr_size(test_bexpr);
  static inline const uint64_t test_stmt_size = stmt_size(test_stmt);
};

#endif // INCLUDED_LARGE_MUTUAL
