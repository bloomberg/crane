#ifndef INCLUDED_LARGE_MUTUAL
#define INCLUDED_LARGE_MUTUAL

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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

    stmt &operator=(const stmt &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    stmt &operator=(stmt &&_other) {
      d_v_ = std::move(_other.d_v_);
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
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const stmt *_src = _frame._src;
        stmt *_dst = _frame._dst;
        if (std::holds_alternative<SAssign>(_src->v())) {
          const auto &_alt = std::get<SAssign>(_src->v());
          _dst->d_v_ = SAssign{_alt.d_a0,
                               _alt.d_a1 ? std::make_unique<LargeMutual::expr>(
                                               _alt.d_a1->clone())
                                         : nullptr};
        } else if (std::holds_alternative<SSeq>(_src->v())) {
          const auto &_alt = std::get<SSeq>(_src->v());
          _dst->d_v_ = SSeq{_alt.d_a0 ? std::make_unique<stmt>() : nullptr,
                            _alt.d_a1 ? std::make_unique<stmt>() : nullptr};
          auto &_dst_alt = std::get<SSeq>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<SIf>(_src->v())) {
          const auto &_alt = std::get<SIf>(_src->v());
          _dst->d_v_ =
              SIf{_alt.d_a0
                      ? std::make_unique<LargeMutual::bexpr>(_alt.d_a0->clone())
                      : nullptr,
                  _alt.d_a1 ? std::make_unique<stmt>() : nullptr,
                  _alt.d_a2 ? std::make_unique<stmt>() : nullptr};
          auto &_dst_alt = std::get<SIf>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        } else if (std::holds_alternative<SWhile>(_src->v())) {
          const auto &_alt = std::get<SWhile>(_src->v());
          _dst->d_v_ = SWhile{_alt.d_a0 ? std::make_unique<LargeMutual::bexpr>(
                                              _alt.d_a0->clone())
                                        : nullptr,
                              _alt.d_a1 ? std::make_unique<stmt>() : nullptr};
          auto &_dst_alt = std::get<SWhile>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          _dst->d_v_ = SSkip{};
        }
      }
      return _out;
    }

    // CREATORS
    static stmt sassign(unsigned int a0, expr a1) {
      return stmt(
          SAssign{std::move(a0), std::make_unique<expr>(std::move(a1))});
    }

    static stmt sseq(stmt a0, stmt a1) {
      return stmt(SSeq{std::make_unique<stmt>(std::move(a0)),
                       std::make_unique<stmt>(std::move(a1))});
    }

    static stmt sif(bexpr a0, stmt a1, stmt a2) {
      return stmt(SIf{std::make_unique<bexpr>(std::move(a0)),
                      std::make_unique<stmt>(std::move(a1)),
                      std::make_unique<stmt>(std::move(a2))});
    }

    static stmt swhile(bexpr a0, stmt a1) {
      return stmt(SWhile{std::make_unique<bexpr>(std::move(a0)),
                         std::make_unique<stmt>(std::move(a1))});
    }

    static stmt sskip() { return stmt(SSkip{}); }

    // MANIPULATORS
    ~stmt() {
      std::vector<std::unique_ptr<stmt>> _stack{};
      auto _drain = [&](stmt &_node) {
        if (std::holds_alternative<SSeq>(_node.d_v_)) {
          auto &_alt = std::get<SSeq>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<SIf>(_node.d_v_)) {
          auto &_alt = std::get<SIf>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
          }
        }
        if (std::holds_alternative<SWhile>(_node.d_v_)) {
          auto &_alt = std::get<SWhile>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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

    expr &operator=(const expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    expr &operator=(expr &&_other) {
      d_v_ = std::move(_other.d_v_);
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
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const expr *_src = _frame._src;
        expr *_dst = _frame._dst;
        if (std::holds_alternative<ENum>(_src->v())) {
          const auto &_alt = std::get<ENum>(_src->v());
          _dst->d_v_ = ENum{_alt.d_a0};
        } else if (std::holds_alternative<EVar>(_src->v())) {
          const auto &_alt = std::get<EVar>(_src->v());
          _dst->d_v_ = EVar{_alt.d_a0};
        } else if (std::holds_alternative<EAdd>(_src->v())) {
          const auto &_alt = std::get<EAdd>(_src->v());
          _dst->d_v_ = EAdd{_alt.d_a0 ? std::make_unique<expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<EAdd>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<EMul>(_src->v())) {
          const auto &_alt = std::get<EMul>(_src->v());
          _dst->d_v_ = EMul{_alt.d_a0 ? std::make_unique<expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<EMul>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<ECond>(_src->v());
          _dst->d_v_ = ECond{_alt.d_a0 ? std::make_unique<LargeMutual::bexpr>(
                                             _alt.d_a0->clone())
                                       : nullptr,
                             _alt.d_a1 ? std::make_unique<expr>() : nullptr,
                             _alt.d_a2 ? std::make_unique<expr>() : nullptr};
          auto &_dst_alt = std::get<ECond>(_dst->d_v_);
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static expr ENum_(unsigned int a0) { return expr(ENum{std::move(a0)}); }

    static expr evar(unsigned int a0) { return expr(EVar{std::move(a0)}); }

    static expr eadd(expr a0, expr a1) {
      return expr(EAdd{std::make_unique<expr>(std::move(a0)),
                       std::make_unique<expr>(std::move(a1))});
    }

    static expr emul(expr a0, expr a1) {
      return expr(EMul{std::make_unique<expr>(std::move(a0)),
                       std::make_unique<expr>(std::move(a1))});
    }

    static expr econd(bexpr a0, expr a1, expr a2) {
      return expr(ECond{std::make_unique<bexpr>(std::move(a0)),
                        std::make_unique<expr>(std::move(a1)),
                        std::make_unique<expr>(std::move(a2))});
    }

    // MANIPULATORS
    ~expr() {
      std::vector<std::unique_ptr<expr>> _stack{};
      auto _drain = [&](expr &_node) {
        if (std::holds_alternative<EAdd>(_node.d_v_)) {
          auto &_alt = std::get<EAdd>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<EMul>(_node.d_v_)) {
          auto &_alt = std::get<EMul>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<ECond>(_node.d_v_)) {
          auto &_alt = std::get<ECond>(_node.d_v_);
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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

    bexpr &operator=(const bexpr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    bexpr &operator=(bexpr &&_other) {
      d_v_ = std::move(_other.d_v_);
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
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const bexpr *_src = _frame._src;
        bexpr *_dst = _frame._dst;
        if (std::holds_alternative<BTrue>(_src->v())) {
          _dst->d_v_ = BTrue{};
        } else if (std::holds_alternative<BFalse>(_src->v())) {
          _dst->d_v_ = BFalse{};
        } else if (std::holds_alternative<BEq>(_src->v())) {
          const auto &_alt = std::get<BEq>(_src->v());
          _dst->d_v_ =
              BEq{_alt.d_a0
                      ? std::make_unique<LargeMutual::expr>(_alt.d_a0->clone())
                      : nullptr,
                  _alt.d_a1
                      ? std::make_unique<LargeMutual::expr>(_alt.d_a1->clone())
                      : nullptr};
        } else if (std::holds_alternative<BLt>(_src->v())) {
          const auto &_alt = std::get<BLt>(_src->v());
          _dst->d_v_ =
              BLt{_alt.d_a0
                      ? std::make_unique<LargeMutual::expr>(_alt.d_a0->clone())
                      : nullptr,
                  _alt.d_a1
                      ? std::make_unique<LargeMutual::expr>(_alt.d_a1->clone())
                      : nullptr};
        } else if (std::holds_alternative<BAnd>(_src->v())) {
          const auto &_alt = std::get<BAnd>(_src->v());
          _dst->d_v_ = BAnd{_alt.d_a0 ? std::make_unique<bexpr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<bexpr>() : nullptr};
          auto &_dst_alt = std::get<BAnd>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else if (std::holds_alternative<BOr>(_src->v())) {
          const auto &_alt = std::get<BOr>(_src->v());
          _dst->d_v_ = BOr{_alt.d_a0 ? std::make_unique<bexpr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<bexpr>() : nullptr};
          auto &_dst_alt = std::get<BOr>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a1) {
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          }
        } else {
          const auto &_alt = std::get<BNot>(_src->v());
          _dst->d_v_ = BNot{_alt.d_a0 ? std::make_unique<bexpr>() : nullptr};
          auto &_dst_alt = std::get<BNot>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static bexpr btrue() { return bexpr(BTrue{}); }

    static bexpr bfalse() { return bexpr(BFalse{}); }

    static bexpr beq(expr a0, expr a1) {
      return bexpr(BEq{std::make_unique<expr>(std::move(a0)),
                       std::make_unique<expr>(std::move(a1))});
    }

    static bexpr blt(expr a0, expr a1) {
      return bexpr(BLt{std::make_unique<expr>(std::move(a0)),
                       std::make_unique<expr>(std::move(a1))});
    }

    static bexpr band(bexpr a0, bexpr a1) {
      return bexpr(BAnd{std::make_unique<bexpr>(std::move(a0)),
                        std::make_unique<bexpr>(std::move(a1))});
    }

    static bexpr bor(bexpr a0, bexpr a1) {
      return bexpr(BOr{std::make_unique<bexpr>(std::move(a0)),
                       std::make_unique<bexpr>(std::move(a1))});
    }

    static bexpr bnot(bexpr a0) {
      return bexpr(BNot{std::make_unique<bexpr>(std::move(a0))});
    }

    // MANIPULATORS
    ~bexpr() {
      std::vector<std::unique_ptr<bexpr>> _stack{};
      auto _drain = [&](bexpr &_node) {
        if (std::holds_alternative<BAnd>(_node.d_v_)) {
          auto &_alt = std::get<BAnd>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<BOr>(_node.d_v_)) {
          auto &_alt = std::get<BOr>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a1) {
            _stack.push_back(std::move(_alt.d_a1));
          }
        }
        if (std::holds_alternative<BNot>(_node.d_v_)) {
          auto &_alt = std::get<BNot>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
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

  static unsigned int expr_size(const expr &e);
  static unsigned int bexpr_size(const bexpr &b);
  static unsigned int stmt_size(const stmt &s);
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
