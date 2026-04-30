#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

    Expr &operator=(const Expr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    Expr &operator=(Expr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    Expr clone() const {
      Expr _out{};

      struct _CloneFrame {
        const Expr *_src;
        Expr *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Expr *_src = _frame._src;
        Expr *_dst = _frame._dst;
        if (std::holds_alternative<Num>(_src->v())) {
          const auto &_alt = std::get<Num>(_src->v());
          _dst->d_v_ = Num{_alt.d_a0};
        } else if (std::holds_alternative<Plus>(_src->v())) {
          const auto &_alt = std::get<Plus>(_src->v());
          _dst->d_v_ = Plus{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<Plus>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else {
          const auto &_alt = std::get<Times>(_src->v());
          _dst->d_v_ = Times{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                             _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<Times>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static Expr num(unsigned int a0) { return Expr(Num{std::move(a0)}); }

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
      std::vector<std::unique_ptr<Expr>> _stack;
      auto _drain = [&](Expr &_node) {
        if (std::holds_alternative<Plus>(_node.d_v_)) {
          auto &_alt = std::get<Plus>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<Times>(_node.d_v_)) {
          auto &_alt = std::get<Times>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int expr_size() const {
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

    unsigned int eval() const {
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

    BExpr &operator=(const BExpr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    BExpr &operator=(BExpr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    BExpr clone() const {
      BExpr _out{};

      struct _CloneFrame {
        const BExpr *_src;
        BExpr *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const BExpr *_src = _frame._src;
        BExpr *_dst = _frame._dst;
        if (std::holds_alternative<BTrue>(_src->v())) {
          const auto &_alt = std::get<BTrue>(_src->v());
          _dst->d_v_ = BTrue{};
        } else if (std::holds_alternative<BFalse>(_src->v())) {
          const auto &_alt = std::get<BFalse>(_src->v());
          _dst->d_v_ = BFalse{};
        } else if (std::holds_alternative<BAnd>(_src->v())) {
          const auto &_alt = std::get<BAnd>(_src->v());
          _dst->d_v_ = BAnd{_alt.d_a0 ? std::make_unique<BExpr>() : nullptr,
                            _alt.d_a1 ? std::make_unique<BExpr>() : nullptr};
          auto &_dst_alt = std::get<BAnd>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else if (std::holds_alternative<BOr>(_src->v())) {
          const auto &_alt = std::get<BOr>(_src->v());
          _dst->d_v_ = BOr{_alt.d_a0 ? std::make_unique<BExpr>() : nullptr,
                           _alt.d_a1 ? std::make_unique<BExpr>() : nullptr};
          auto &_dst_alt = std::get<BOr>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else {
          const auto &_alt = std::get<BNot>(_src->v());
          _dst->d_v_ = BNot{_alt.d_a0 ? std::make_unique<BExpr>() : nullptr};
          auto &_dst_alt = std::get<BNot>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
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
      std::vector<std::unique_ptr<BExpr>> _stack;
      auto _drain = [&](BExpr &_node) {
        if (std::holds_alternative<BAnd>(_node.d_v_)) {
          auto &_alt = std::get<BAnd>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<BOr>(_node.d_v_)) {
          auto &_alt = std::get<BOr>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<BNot>(_node.d_v_)) {
          auto &_alt = std::get<BNot>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    bool beval() const {
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

    AExpr &operator=(const AExpr &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    AExpr &operator=(AExpr &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    AExpr clone() const {
      AExpr _out{};

      struct _CloneFrame {
        const AExpr *_src;
        AExpr *_dst;
      };

      std::vector<_CloneFrame> _stack;
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const AExpr *_src = _frame._src;
        AExpr *_dst = _frame._dst;
        if (std::holds_alternative<ANum>(_src->v())) {
          const auto &_alt = std::get<ANum>(_src->v());
          _dst->d_v_ = ANum{_alt.d_a0};
        } else if (std::holds_alternative<APlus>(_src->v())) {
          const auto &_alt = std::get<APlus>(_src->v());
          _dst->d_v_ = APlus{_alt.d_a0 ? std::make_unique<AExpr>() : nullptr,
                             _alt.d_a1 ? std::make_unique<AExpr>() : nullptr};
          auto &_dst_alt = std::get<APlus>(_dst->d_v_);
          if (_alt.d_a0)
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        } else {
          const auto &_alt = std::get<AIf>(_src->v());
          _dst->d_v_ =
              AIf{_alt.d_a0, _alt.d_a1 ? std::make_unique<AExpr>() : nullptr,
                  _alt.d_a2 ? std::make_unique<AExpr>() : nullptr};
          auto &_dst_alt = std::get<AIf>(_dst->d_v_);
          if (_alt.d_a1)
            _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
          if (_alt.d_a2)
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
        }
      }
      return _out;
    }

    // CREATORS
    static AExpr anum(unsigned int a0) { return AExpr(ANum{std::move(a0)}); }

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
      std::vector<std::unique_ptr<AExpr>> _stack;
      auto _drain = [&](AExpr &_node) {
        if (std::holds_alternative<APlus>(_node.d_v_)) {
          auto &_alt = std::get<APlus>(_node.d_v_);
          if (_alt.d_a0)
            _stack.push_back(std::move(_alt.d_a0));
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
        }
        if (std::holds_alternative<AIf>(_node.d_v_)) {
          auto &_alt = std::get<AIf>(_node.d_v_);
          if (_alt.d_a1)
            _stack.push_back(std::move(_alt.d_a1));
          if (_alt.d_a2)
            _stack.push_back(std::move(_alt.d_a2));
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node)
          _drain(*_node);
      }
    }

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }

    unsigned int aeval() const {
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
