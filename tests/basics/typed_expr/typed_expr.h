#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

enum class Ty { TNAT, TBOOL };

struct Expr {
  // TYPES
  struct ENat {
    unsigned int a0;
  };

  struct EBool {
    bool a0;
  };

  struct EAdd {
    std::unique_ptr<Expr> a0;
    std::unique_ptr<Expr> a1;
  };

  struct EEq {
    std::unique_ptr<Expr> a0;
    std::unique_ptr<Expr> a1;
  };

  struct EIf {
    Ty t;
    std::unique_ptr<Expr> a1;
    std::unique_ptr<Expr> a2;
    std::unique_ptr<Expr> a3;
  };

  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Expr() {}

  explicit Expr(ENat _v) : v_(std::move(_v)) {}

  explicit Expr(EBool _v) : v_(std::move(_v)) {}

  explicit Expr(EAdd _v) : v_(std::move(_v)) {}

  explicit Expr(EEq _v) : v_(std::move(_v)) {}

  explicit Expr(EIf _v) : v_(std::move(_v)) {}

  Expr(const Expr &_other) : v_(std::move(_other.clone().v_)) {}

  Expr(Expr &&_other) : v_(std::move(_other.v_)) {}

  Expr &operator=(const Expr &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Expr &operator=(Expr &&_other) {
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
      if (std::holds_alternative<ENat>(_src->v())) {
        const auto &_alt = std::get<ENat>(_src->v());
        _dst->v_ = ENat{_alt.a0};
      } else if (std::holds_alternative<EBool>(_src->v())) {
        const auto &_alt = std::get<EBool>(_src->v());
        _dst->v_ = EBool{_alt.a0};
      } else if (std::holds_alternative<EAdd>(_src->v())) {
        const auto &_alt = std::get<EAdd>(_src->v());
        _dst->v_ = EAdd{_alt.a0 ? std::make_unique<Expr>() : nullptr,
                        _alt.a1 ? std::make_unique<Expr>() : nullptr};
        auto &_dst_alt = std::get<EAdd>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      } else if (std::holds_alternative<EEq>(_src->v())) {
        const auto &_alt = std::get<EEq>(_src->v());
        _dst->v_ = EEq{_alt.a0 ? std::make_unique<Expr>() : nullptr,
                       _alt.a1 ? std::make_unique<Expr>() : nullptr};
        auto &_dst_alt = std::get<EEq>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      } else {
        const auto &_alt = std::get<EIf>(_src->v());
        _dst->v_ = EIf{_alt.t, _alt.a1 ? std::make_unique<Expr>() : nullptr,
                       _alt.a2 ? std::make_unique<Expr>() : nullptr,
                       _alt.a3 ? std::make_unique<Expr>() : nullptr};
        auto &_dst_alt = std::get<EIf>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
        if (_alt.a2) {
          _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
        }
        if (_alt.a3) {
          _stack.push_back({_alt.a3.get(), _dst_alt.a3.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Expr enat(unsigned int a0) { return Expr(ENat{a0}); }

  static Expr ebool(bool a0) { return Expr(EBool{a0}); }

  static Expr eadd(Expr a0, Expr a1) {
    return Expr(EAdd{std::make_unique<Expr>(std::move(a0)),
                     std::make_unique<Expr>(std::move(a1))});
  }

  static Expr eeq(Expr a0, Expr a1) {
    return Expr(EEq{std::make_unique<Expr>(std::move(a0)),
                    std::make_unique<Expr>(std::move(a1))});
  }

  static Expr eif(Ty t, Expr a1, Expr a2, Expr a3) {
    return Expr(EIf{t, std::make_unique<Expr>(std::move(a1)),
                    std::make_unique<Expr>(std::move(a2)),
                    std::make_unique<Expr>(std::move(a3))});
  }

  // MANIPULATORS
  ~Expr() {
    std::vector<std::unique_ptr<Expr>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Expr &_node) {
      if (std::holds_alternative<EAdd>(_node.v_)) {
        auto &_alt = std::get<EAdd>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
      if (std::holds_alternative<EEq>(_node.v_)) {
        auto &_alt = std::get<EEq>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
      if (std::holds_alternative<EIf>(_node.v_)) {
        auto &_alt = std::get<EIf>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
        if (_alt.a2) {
          _stack.push_back(std::move(_alt.a2));
        }
        if (_alt.a3) {
          _stack.push_back(std::move(_alt.a3));
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

  std::any eval(Ty) const {
    if (std::holds_alternative<typename Expr::ENat>(this->v())) {
      const auto &[a0] = std::get<typename Expr::ENat>(this->v());
      return a0;
    } else if (std::holds_alternative<typename Expr::EBool>(this->v())) {
      const auto &[a0] = std::get<typename Expr::EBool>(this->v());
      return a0;
    } else if (std::holds_alternative<typename Expr::EAdd>(this->v())) {
      const auto &[a0, a1] = std::get<typename Expr::EAdd>(this->v());
      return (std::any_cast<unsigned int>((*a0).eval(Ty::TNAT)) +
              std::any_cast<unsigned int>((*a1).eval(Ty::TNAT)));
    } else if (std::holds_alternative<typename Expr::EEq>(this->v())) {
      const auto &[a0, a1] = std::get<typename Expr::EEq>(this->v());
      return std::any_cast<unsigned int>((*a0).eval(Ty::TNAT)) ==
             std::any_cast<unsigned int>((*a1).eval(Ty::TNAT));
    } else {
      const auto &[t, a1, a2, a3] = std::get<typename Expr::EIf>(this->v());
      if (std::any_cast<bool>((*a1).eval(Ty::TBOOL))) {
        return (*a2).eval(t);
      } else {
        return (*a3).eval(t);
      }
    }
  }
};

#endif // INCLUDED_TYPED_EXPR
