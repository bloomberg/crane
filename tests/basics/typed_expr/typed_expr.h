#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Ty { e_TNAT, e_TBOOL };

struct Expr {
  // TYPES
  struct ENat {
    unsigned int d_a0;
  };

  struct EBool {
    bool d_a0;
  };

  struct EAdd {
    std::unique_ptr<Expr> d_a0;
    std::unique_ptr<Expr> d_a1;
  };

  struct EEq {
    std::unique_ptr<Expr> d_a0;
    std::unique_ptr<Expr> d_a1;
  };

  struct EIf {
    Ty d_t;
    std::unique_ptr<Expr> d_a1;
    std::unique_ptr<Expr> d_a2;
    std::unique_ptr<Expr> d_a3;
  };

  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Expr() {}

  explicit Expr(ENat _v) : d_v_(std::move(_v)) {}

  explicit Expr(EBool _v) : d_v_(std::move(_v)) {}

  explicit Expr(EAdd _v) : d_v_(std::move(_v)) {}

  explicit Expr(EEq _v) : d_v_(std::move(_v)) {}

  explicit Expr(EIf _v) : d_v_(std::move(_v)) {}

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

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Expr *_src = _frame._src;
      Expr *_dst = _frame._dst;
      if (std::holds_alternative<ENat>(_src->v())) {
        const auto &_alt = std::get<ENat>(_src->v());
        _dst->d_v_ = ENat{_alt.d_a0};
      } else if (std::holds_alternative<EBool>(_src->v())) {
        const auto &_alt = std::get<EBool>(_src->v());
        _dst->d_v_ = EBool{_alt.d_a0};
      } else if (std::holds_alternative<EAdd>(_src->v())) {
        const auto &_alt = std::get<EAdd>(_src->v());
        _dst->d_v_ = EAdd{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                          _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
        auto &_dst_alt = std::get<EAdd>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      } else if (std::holds_alternative<EEq>(_src->v())) {
        const auto &_alt = std::get<EEq>(_src->v());
        _dst->d_v_ = EEq{_alt.d_a0 ? std::make_unique<Expr>() : nullptr,
                         _alt.d_a1 ? std::make_unique<Expr>() : nullptr};
        auto &_dst_alt = std::get<EEq>(_dst->d_v_);
        if (_alt.d_a0) {
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
        }
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      } else {
        const auto &_alt = std::get<EIf>(_src->v());
        _dst->d_v_ =
            EIf{_alt.d_t, _alt.d_a1 ? std::make_unique<Expr>() : nullptr,
                _alt.d_a2 ? std::make_unique<Expr>() : nullptr,
                _alt.d_a3 ? std::make_unique<Expr>() : nullptr};
        auto &_dst_alt = std::get<EIf>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
        if (_alt.d_a2) {
          _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
        }
        if (_alt.d_a3) {
          _stack.push_back({_alt.d_a3.get(), _dst_alt.d_a3.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Expr enat(unsigned int a0) { return Expr(ENat{std::move(a0)}); }

  static Expr ebool(bool a0) { return Expr(EBool{std::move(a0)}); }

  static Expr eadd(Expr a0, Expr a1) {
    return Expr(EAdd{std::make_unique<Expr>(std::move(a0)),
                     std::make_unique<Expr>(std::move(a1))});
  }

  static Expr eeq(Expr a0, Expr a1) {
    return Expr(EEq{std::make_unique<Expr>(std::move(a0)),
                    std::make_unique<Expr>(std::move(a1))});
  }

  static Expr eif(Ty t, Expr a1, Expr a2, Expr a3) {
    return Expr(EIf{std::move(t), std::make_unique<Expr>(std::move(a1)),
                    std::make_unique<Expr>(std::move(a2)),
                    std::make_unique<Expr>(std::move(a3))});
  }

  // MANIPULATORS
  ~Expr() {
    std::vector<std::unique_ptr<Expr>> _stack{};
    auto _drain = [&](Expr &_node) {
      if (std::holds_alternative<EAdd>(_node.d_v_)) {
        auto &_alt = std::get<EAdd>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
      if (std::holds_alternative<EEq>(_node.d_v_)) {
        auto &_alt = std::get<EEq>(_node.d_v_);
        if (_alt.d_a0) {
          _stack.push_back(std::move(_alt.d_a0));
        }
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
      if (std::holds_alternative<EIf>(_node.d_v_)) {
        auto &_alt = std::get<EIf>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
        if (_alt.d_a2) {
          _stack.push_back(std::move(_alt.d_a2));
        }
        if (_alt.d_a3) {
          _stack.push_back(std::move(_alt.d_a3));
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

  std::any eval(const Ty) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Expr::ENat>(_sv.v())) {
      const auto &[d_a0] = std::get<typename Expr::ENat>(_sv.v());
      return d_a0;
    } else if (std::holds_alternative<typename Expr::EBool>(_sv.v())) {
      const auto &[d_a0] = std::get<typename Expr::EBool>(_sv.v());
      return d_a0;
    } else if (std::holds_alternative<typename Expr::EAdd>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<typename Expr::EAdd>(_sv.v());
      return (std::any_cast<unsigned int>((*(d_a0)).eval(Ty::e_TNAT)) +
              std::any_cast<unsigned int>((*(d_a1)).eval(Ty::e_TNAT)));
    } else if (std::holds_alternative<typename Expr::EEq>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<typename Expr::EEq>(_sv.v());
      return std::any_cast<unsigned int>((*(d_a0)).eval(Ty::e_TNAT)) ==
             std::any_cast<unsigned int>((*(d_a1)).eval(Ty::e_TNAT));
    } else {
      const auto &[d_t, d_a1, d_a2, d_a3] =
          std::get<typename Expr::EIf>(_sv.v());
      if (std::any_cast<bool>((*(d_a1)).eval(Ty::e_TBOOL))) {
        return (*(d_a2)).eval(d_t);
      } else {
        return (*(d_a3)).eval(d_t);
      }
    }
  }
};

#endif // INCLUDED_TYPED_EXPR
