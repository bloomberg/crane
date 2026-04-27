#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

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
  __attribute__((pure)) Expr clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<ENat>(_sv.v())) {
      const auto &[d_a0] = std::get<ENat>(_sv.v());
      return Expr(ENat{d_a0});
    } else if (std::holds_alternative<EBool>(_sv.v())) {
      const auto &[d_a0] = std::get<EBool>(_sv.v());
      return Expr(EBool{d_a0});
    } else if (std::holds_alternative<EAdd>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<EAdd>(_sv.v());
      return Expr(EAdd{d_a0 ? std::make_unique<Expr>(d_a0->clone()) : nullptr,
                       d_a1 ? std::make_unique<Expr>(d_a1->clone()) : nullptr});
    } else if (std::holds_alternative<EEq>(_sv.v())) {
      const auto &[d_a0, d_a1] = std::get<EEq>(_sv.v());
      return Expr(EEq{d_a0 ? std::make_unique<Expr>(d_a0->clone()) : nullptr,
                      d_a1 ? std::make_unique<Expr>(d_a1->clone()) : nullptr});
    } else {
      const auto &[d_t, d_a1, d_a2, d_a3] = std::get<EIf>(_sv.v());
      return Expr(EIf{d_t,
                      d_a1 ? std::make_unique<Expr>(d_a1->clone()) : nullptr,
                      d_a2 ? std::make_unique<Expr>(d_a2->clone()) : nullptr,
                      d_a3 ? std::make_unique<Expr>(d_a3->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Expr enat(unsigned int a0) {
    return Expr(ENat{std::move(a0)});
  }

  __attribute__((pure)) static Expr ebool(bool a0) {
    return Expr(EBool{std::move(a0)});
  }

  __attribute__((pure)) static Expr eadd(const Expr &a0, const Expr &a1) {
    return Expr(EAdd{std::make_unique<Expr>(a0), std::make_unique<Expr>(a1)});
  }

  __attribute__((pure)) static Expr eeq(const Expr &a0, const Expr &a1) {
    return Expr(EEq{std::make_unique<Expr>(a0), std::make_unique<Expr>(a1)});
  }

  __attribute__((pure)) static Expr eif(Ty t, const Expr &a1, const Expr &a2,
                                        const Expr &a3) {
    return Expr(EIf{std::move(t), std::make_unique<Expr>(a1),
                    std::make_unique<Expr>(a2), std::make_unique<Expr>(a3)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

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
