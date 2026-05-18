#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct WhereClause {
  struct Expr {
    // TYPES
    struct Num {
      uint64_t a0;
    };

    struct Plus {
      std::unique_ptr<Expr> a0;
      std::unique_ptr<Expr> a1;
    };

    struct Times {
      std::unique_ptr<Expr> a0;
      std::unique_ptr<Expr> a1;
    };

    using variant_t = std::variant<Num, Plus, Times>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Expr() {}

    explicit Expr(Num _v) : v_(std::move(_v)) {}

    explicit Expr(Plus _v) : v_(std::move(_v)) {}

    explicit Expr(Times _v) : v_(std::move(_v)) {}

    Expr(const Expr &_other) : v_(std::move(_other.clone().v_)) {}

    Expr(Expr &&_other) noexcept : v_(std::move(_other.v_)) {}

    Expr &operator=(const Expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Expr &operator=(Expr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Expr clone() const {
      Expr _out{};

      struct _CloneFrame {
        const Expr *_src;
        Expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Expr *_src = _frame._src;
        Expr *_dst = _frame._dst;
        if (std::holds_alternative<Num>(_src->v())) {
          const auto &_alt = std::get<Num>(_src->v());
          _dst->v_ = Num{_alt.a0};
        } else if (std::holds_alternative<Plus>(_src->v())) {
          const auto &_alt = std::get<Plus>(_src->v());
          _dst->v_ = Plus{_alt.a0 ? std::make_unique<Expr>() : nullptr,
                          _alt.a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<Plus>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<Times>(_src->v());
          _dst->v_ = Times{_alt.a0 ? std::make_unique<Expr>() : nullptr,
                           _alt.a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<Times>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static Expr num(uint64_t a0) { return Expr(Num{a0}); }

    static Expr plus(Expr a0, Expr a1) {
      return Expr(Plus{std::make_unique<Expr>(std::move(a0)),
                       std::make_unique<Expr>(std::move(a1))});
    }

    static Expr times(Expr a0, Expr a1) {
      return Expr(Times{std::make_unique<Expr>(std::move(a0)),
                        std::make_unique<Expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~Expr() {
      std::vector<std::unique_ptr<Expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](Expr &_node) {
        if (std::holds_alternative<Plus>(_node.v_)) {
          auto &_alt = std::get<Plus>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<Times>(_node.v_)) {
          auto &_alt = std::get<Times>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t expr_size() const {
      if (std::holds_alternative<typename Expr::Num>(this->v())) {
        return UINT64_C(1);
      } else if (std::holds_alternative<typename Expr::Plus>(this->v())) {
        const auto &[a0, a1] = std::get<typename Expr::Plus>(this->v());
        return ((UINT64_C(1) + a0->expr_size()) + a1->expr_size());
      } else {
        const auto &[a0, a1] = std::get<typename Expr::Times>(this->v());
        return ((UINT64_C(1) + a0->expr_size()) + a1->expr_size());
      }
    }

    uint64_t eval() const {
      if (std::holds_alternative<typename Expr::Num>(this->v())) {
        const auto &[a0] = std::get<typename Expr::Num>(this->v());
        return a0;
      } else if (std::holds_alternative<typename Expr::Plus>(this->v())) {
        const auto &[a0, a1] = std::get<typename Expr::Plus>(this->v());
        return (a0->eval() + a1->eval());
      } else {
        const auto &[a0, a1] = std::get<typename Expr::Times>(this->v());
        return (a0->eval() * a1->eval());
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, Expr &, T1 &, Expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, Expr &, T1 &, Expr &, T1 &>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename Expr::Num>(this->v())) {
        const auto &[a0] = std::get<typename Expr::Num>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename Expr::Plus>(this->v())) {
        const auto &[a0, a1] = std::get<typename Expr::Plus>(this->v());
        return f0(*a0, a0->template Expr_rec<T1>(f, f0, f1), *a1,
                  a1->template Expr_rec<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1] = std::get<typename Expr::Times>(this->v());
        return f1(*a0, a0->template Expr_rec<T1>(f, f0, f1), *a1,
                  a1->template Expr_rec<T1>(f, f0, f1));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, Expr &, T1 &, Expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, Expr &, T1 &, Expr &, T1 &>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename Expr::Num>(this->v())) {
        const auto &[a0] = std::get<typename Expr::Num>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename Expr::Plus>(this->v())) {
        const auto &[a0, a1] = std::get<typename Expr::Plus>(this->v());
        return f0(*a0, a0->template Expr_rect<T1>(f, f0, f1), *a1,
                  a1->template Expr_rect<T1>(f, f0, f1));
      } else {
        const auto &[a0, a1] = std::get<typename Expr::Times>(this->v());
        return f1(*a0, a0->template Expr_rect<T1>(f, f0, f1), *a1,
                  a1->template Expr_rect<T1>(f, f0, f1));
      }
    }
  };

  struct BExpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::unique_ptr<BExpr> a0;
      std::unique_ptr<BExpr> a1;
    };

    struct BOr {
      std::unique_ptr<BExpr> a0;
      std::unique_ptr<BExpr> a1;
    };

    struct BNot {
      std::unique_ptr<BExpr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    BExpr() {}

    explicit BExpr(BTrue _v) : v_(_v) {}

    explicit BExpr(BFalse _v) : v_(_v) {}

    explicit BExpr(BAnd _v) : v_(std::move(_v)) {}

    explicit BExpr(BOr _v) : v_(std::move(_v)) {}

    explicit BExpr(BNot _v) : v_(std::move(_v)) {}

    BExpr(const BExpr &_other) : v_(std::move(_other.clone().v_)) {}

    BExpr(BExpr &&_other) noexcept : v_(std::move(_other.v_)) {}

    BExpr &operator=(const BExpr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    BExpr &operator=(BExpr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    BExpr clone() const {
      BExpr _out{};

      struct _CloneFrame {
        const BExpr *_src;
        BExpr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const BExpr *_src = _frame._src;
        BExpr *_dst = _frame._dst;
        if (std::holds_alternative<BTrue>(_src->v())) {
          _dst->v_ = BTrue{};
        } else if (std::holds_alternative<BFalse>(_src->v())) {
          _dst->v_ = BFalse{};
        } else if (std::holds_alternative<BAnd>(_src->v())) {
          const auto &_alt = std::get<BAnd>(_src->v());
          _dst->v_ = BAnd{_alt.a0 ? std::make_unique<BExpr>() : nullptr,
                          _alt.a1 ? std::make_unique<BExpr>() : nullptr};
          auto &_dst_alt = std::get<BAnd>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else if (std::holds_alternative<BOr>(_src->v())) {
          const auto &_alt = std::get<BOr>(_src->v());
          _dst->v_ = BOr{_alt.a0 ? std::make_unique<BExpr>() : nullptr,
                         _alt.a1 ? std::make_unique<BExpr>() : nullptr};
          auto &_dst_alt = std::get<BOr>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<BNot>(_src->v());
          _dst->v_ = BNot{_alt.a0 ? std::make_unique<BExpr>() : nullptr};
          auto &_dst_alt = std::get<BNot>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static BExpr btrue() { return BExpr(BTrue{}); }

    static BExpr bfalse() { return BExpr(BFalse{}); }

    static BExpr band(BExpr a0, BExpr a1) {
      return BExpr(BAnd{std::make_unique<BExpr>(std::move(a0)),
                        std::make_unique<BExpr>(std::move(a1))});
    }

    static BExpr bor(BExpr a0, BExpr a1) {
      return BExpr(BOr{std::make_unique<BExpr>(std::move(a0)),
                       std::make_unique<BExpr>(std::move(a1))});
    }

    static BExpr bnot(BExpr a0) {
      return BExpr(BNot{std::make_unique<BExpr>(std::move(a0))});
    }

    // MANIPULATORS
    ~BExpr() {
      std::vector<std::unique_ptr<BExpr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](BExpr &_node) {
        if (std::holds_alternative<BAnd>(_node.v_)) {
          auto &_alt = std::get<BAnd>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<BOr>(_node.v_)) {
          auto &_alt = std::get<BOr>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<BNot>(_node.v_)) {
          auto &_alt = std::get<BNot>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool beval() const {
      if (std::holds_alternative<typename BExpr::BTrue>(this->v())) {
        return true;
      } else if (std::holds_alternative<typename BExpr::BFalse>(this->v())) {
        return false;
      } else if (std::holds_alternative<typename BExpr::BAnd>(this->v())) {
        const auto &[a0, a1] = std::get<typename BExpr::BAnd>(this->v());
        return (a0->beval() && a1->beval());
      } else if (std::holds_alternative<typename BExpr::BOr>(this->v())) {
        const auto &[a0, a1] = std::get<typename BExpr::BOr>(this->v());
        return (a0->beval() || a1->beval());
      } else {
        const auto &[a0] = std::get<typename BExpr::BNot>(this->v());
        return !(a0->beval());
      }
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, BExpr &, T1 &>
    T1 BExpr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      if (std::holds_alternative<typename BExpr::BTrue>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename BExpr::BFalse>(this->v())) {
        return f0;
      } else if (std::holds_alternative<typename BExpr::BAnd>(this->v())) {
        const auto &[a0, a1] = std::get<typename BExpr::BAnd>(this->v());
        return f1(*a0, a0->template BExpr_rec<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template BExpr_rec<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename BExpr::BOr>(this->v())) {
        const auto &[a0, a1] = std::get<typename BExpr::BOr>(this->v());
        return f2(*a0, a0->template BExpr_rec<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template BExpr_rec<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[a0] = std::get<typename BExpr::BNot>(this->v());
        return f3(*a0, a0->template BExpr_rec<T1>(f, f0, f1, f2, f3));
      }
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, BExpr &, T1 &>
    T1 BExpr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      if (std::holds_alternative<typename BExpr::BTrue>(this->v())) {
        return f;
      } else if (std::holds_alternative<typename BExpr::BFalse>(this->v())) {
        return f0;
      } else if (std::holds_alternative<typename BExpr::BAnd>(this->v())) {
        const auto &[a0, a1] = std::get<typename BExpr::BAnd>(this->v());
        return f1(*a0, a0->template BExpr_rect<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template BExpr_rect<T1>(f, f0, f1, f2, f3));
      } else if (std::holds_alternative<typename BExpr::BOr>(this->v())) {
        const auto &[a0, a1] = std::get<typename BExpr::BOr>(this->v());
        return f2(*a0, a0->template BExpr_rect<T1>(f, f0, f1, f2, f3), *a1,
                  a1->template BExpr_rect<T1>(f, f0, f1, f2, f3));
      } else {
        const auto &[a0] = std::get<typename BExpr::BNot>(this->v());
        return f3(*a0, a0->template BExpr_rect<T1>(f, f0, f1, f2, f3));
      }
    }
  };

  struct AExpr {
    // TYPES
    struct ANum {
      uint64_t a0;
    };

    struct APlus {
      std::unique_ptr<AExpr> a0;
      std::unique_ptr<AExpr> a1;
    };

    struct AIf {
      BExpr a0;
      std::unique_ptr<AExpr> a1;
      std::unique_ptr<AExpr> a2;
    };

    using variant_t = std::variant<ANum, APlus, AIf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    AExpr() {}

    explicit AExpr(ANum _v) : v_(std::move(_v)) {}

    explicit AExpr(APlus _v) : v_(std::move(_v)) {}

    explicit AExpr(AIf _v) : v_(std::move(_v)) {}

    AExpr(const AExpr &_other) : v_(std::move(_other.clone().v_)) {}

    AExpr(AExpr &&_other) noexcept : v_(std::move(_other.v_)) {}

    AExpr &operator=(const AExpr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    AExpr &operator=(AExpr &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    AExpr clone() const {
      AExpr _out{};

      struct _CloneFrame {
        const AExpr *_src;
        AExpr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const AExpr *_src = _frame._src;
        AExpr *_dst = _frame._dst;
        if (std::holds_alternative<ANum>(_src->v())) {
          const auto &_alt = std::get<ANum>(_src->v());
          _dst->v_ = ANum{_alt.a0};
        } else if (std::holds_alternative<APlus>(_src->v())) {
          const auto &_alt = std::get<APlus>(_src->v());
          _dst->v_ = APlus{_alt.a0 ? std::make_unique<AExpr>() : nullptr,
                           _alt.a1 ? std::make_unique<AExpr>() : nullptr};
          auto &_dst_alt = std::get<APlus>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        } else {
          const auto &_alt = std::get<AIf>(_src->v());
          _dst->v_ = AIf{_alt.a0.clone(),
                         _alt.a1 ? std::make_unique<AExpr>() : nullptr,
                         _alt.a2 ? std::make_unique<AExpr>() : nullptr};
          auto &_dst_alt = std::get<AIf>(_dst->v_);
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
    static AExpr anum(uint64_t a0) { return AExpr(ANum{a0}); }

    static AExpr aplus(AExpr a0, AExpr a1) {
      return AExpr(APlus{std::make_unique<AExpr>(std::move(a0)),
                         std::make_unique<AExpr>(std::move(a1))});
    }

    static AExpr aif(BExpr a0, AExpr a1, AExpr a2) {
      return AExpr(AIf{std::move(a0), std::make_unique<AExpr>(std::move(a1)),
                       std::make_unique<AExpr>(std::move(a2))});
    }

    // MANIPULATORS
    ~AExpr() {
      std::vector<std::unique_ptr<AExpr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](AExpr &_node) {
        if (std::holds_alternative<APlus>(_node.v_)) {
          auto &_alt = std::get<APlus>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
        }
        if (std::holds_alternative<AIf>(_node.v_)) {
          auto &_alt = std::get<AIf>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t aeval() const {
      if (std::holds_alternative<typename AExpr::ANum>(this->v())) {
        const auto &[a0] = std::get<typename AExpr::ANum>(this->v());
        return a0;
      } else if (std::holds_alternative<typename AExpr::APlus>(this->v())) {
        const auto &[a0, a1] = std::get<typename AExpr::APlus>(this->v());
        return (a0->aeval() + a1->aeval());
      } else {
        const auto &[a0, a1, a2] = std::get<typename AExpr::AIf>(this->v());
        if (a0.beval()) {
          return a1->aeval();
        } else {
          return a2->aeval();
        }
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, AExpr &, T1 &, AExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, BExpr &, AExpr &, T1 &, AExpr &,
                                     T1 &>
    T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename AExpr::ANum>(this->v())) {
        const auto &[a0] = std::get<typename AExpr::ANum>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename AExpr::APlus>(this->v())) {
        const auto &[a2, a3] = std::get<typename AExpr::APlus>(this->v());
        return f0(*a2, a2->template AExpr_rec<T1>(f, f0, f1), *a3,
                  a3->template AExpr_rec<T1>(f, f0, f1));
      } else {
        const auto &[a2, a3, a4] = std::get<typename AExpr::AIf>(this->v());
        return f1(a2, *a3, a3->template AExpr_rec<T1>(f, f0, f1), *a4,
                  a4->template AExpr_rec<T1>(f, f0, f1));
      }
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, AExpr &, T1 &, AExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, BExpr &, AExpr &, T1 &, AExpr &,
                                     T1 &>
    T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename AExpr::ANum>(this->v())) {
        const auto &[a0] = std::get<typename AExpr::ANum>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename AExpr::APlus>(this->v())) {
        const auto &[a2, a3] = std::get<typename AExpr::APlus>(this->v());
        return f0(*a2, a2->template AExpr_rect<T1>(f, f0, f1), *a3,
                  a3->template AExpr_rect<T1>(f, f0, f1));
      } else {
        const auto &[a2, a3, a4] = std::get<typename AExpr::AIf>(this->v());
        return f1(a2, *a3, a3->template AExpr_rect<T1>(f, f0, f1), *a4,
                  a4->template AExpr_rect<T1>(f, f0, f1));
      }
    }
  };

  static inline const uint64_t test_eval_plus =
      Expr::plus(Expr::num(UINT64_C(3)), Expr::num(UINT64_C(4))).eval();
  static inline const uint64_t test_eval_times =
      Expr::times(Expr::num(UINT64_C(5)), Expr::num(UINT64_C(6))).eval();
  static inline const uint64_t test_eval_nested =
      Expr::plus(Expr::times(Expr::num(UINT64_C(2)), Expr::num(UINT64_C(3))),
                 Expr::num(UINT64_C(1)))
          .eval();
  static inline const uint64_t test_size =
      Expr::plus(Expr::times(Expr::num(UINT64_C(2)), Expr::num(UINT64_C(3))),
                 Expr::num(UINT64_C(1)))
          .expr_size();
  static inline const bool test_beval =
      BExpr::band(BExpr::btrue(), BExpr::bnot(BExpr::bfalse())).beval();
  static inline const uint64_t test_aeval =
      AExpr::aif(BExpr::band(BExpr::btrue(), BExpr::btrue()),
                 AExpr::anum(UINT64_C(10)), AExpr::anum(UINT64_C(20)))
          .aeval();
};

#endif // INCLUDED_WHERE_CLAUSE
