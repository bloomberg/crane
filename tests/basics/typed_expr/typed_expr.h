#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
    std::shared_ptr<Expr> d_a0;
    std::shared_ptr<Expr> d_a1;
  };

  struct EEq {
    std::shared_ptr<Expr> d_a0;
    std::shared_ptr<Expr> d_a1;
  };

  struct EIf {
    Ty d_t;
    std::shared_ptr<Expr> d_a1;
    std::shared_ptr<Expr> d_a2;
    std::shared_ptr<Expr> d_a3;
  };

  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Expr(ENat _v) : d_v_(std::move(_v)) {}

  explicit Expr(EBool _v) : d_v_(std::move(_v)) {}

  explicit Expr(EAdd _v) : d_v_(std::move(_v)) {}

  explicit Expr(EEq _v) : d_v_(std::move(_v)) {}

  explicit Expr(EIf _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Expr> enat(unsigned int a0) {
    return std::make_shared<Expr>(ENat{std::move(a0)});
  }

  static std::shared_ptr<Expr> ebool(bool a0) {
    return std::make_shared<Expr>(EBool{std::move(a0)});
  }

  static std::shared_ptr<Expr> eadd(const std::shared_ptr<Expr> &a0,
                                    const std::shared_ptr<Expr> &a1) {
    return std::make_shared<Expr>(EAdd{a0, a1});
  }

  static std::shared_ptr<Expr> eadd(std::shared_ptr<Expr> &&a0,
                                    std::shared_ptr<Expr> &&a1) {
    return std::make_shared<Expr>(EAdd{std::move(a0), std::move(a1)});
  }

  static std::shared_ptr<Expr> eeq(const std::shared_ptr<Expr> &a0,
                                   const std::shared_ptr<Expr> &a1) {
    return std::make_shared<Expr>(EEq{a0, a1});
  }

  static std::shared_ptr<Expr> eeq(std::shared_ptr<Expr> &&a0,
                                   std::shared_ptr<Expr> &&a1) {
    return std::make_shared<Expr>(EEq{std::move(a0), std::move(a1)});
  }

  static std::shared_ptr<Expr> eif(Ty t, const std::shared_ptr<Expr> &a1,
                                   const std::shared_ptr<Expr> &a2,
                                   const std::shared_ptr<Expr> &a3) {
    return std::make_shared<Expr>(EIf{std::move(t), a1, a2, a3});
  }

  static std::shared_ptr<Expr> eif(Ty t, std::shared_ptr<Expr> &&a1,
                                   std::shared_ptr<Expr> &&a2,
                                   std::shared_ptr<Expr> &&a3) {
    return std::make_shared<Expr>(
        EIf{std::move(t), std::move(a1), std::move(a2), std::move(a3)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::any eval(const Ty) const {
    if (std::holds_alternative<typename Expr::ENat>(this->v())) {
      const auto &[d_a0] = std::get<typename Expr::ENat>(this->v());
      return d_a0;
    } else if (std::holds_alternative<typename Expr::EBool>(this->v())) {
      const auto &[d_a0] = std::get<typename Expr::EBool>(this->v());
      return d_a0;
    } else if (std::holds_alternative<typename Expr::EAdd>(this->v())) {
      const auto &[d_a0, d_a1] = std::get<typename Expr::EAdd>(this->v());
      return (std::any_cast<unsigned int>(d_a0->eval(Ty::e_TNAT)) +
              std::any_cast<unsigned int>(d_a1->eval(Ty::e_TNAT)));
    } else if (std::holds_alternative<typename Expr::EEq>(this->v())) {
      const auto &[d_a0, d_a1] = std::get<typename Expr::EEq>(this->v());
      return std::any_cast<unsigned int>(d_a0->eval(Ty::e_TNAT)) ==
             std::any_cast<unsigned int>(d_a1->eval(Ty::e_TNAT));
    } else {
      const auto &[d_t, d_a1, d_a2, d_a3] =
          std::get<typename Expr::EIf>(this->v());
      if (std::any_cast<bool>(d_a1->eval(Ty::e_TBOOL))) {
        return d_a2->eval(d_t);
      } else {
        return d_a3->eval(d_t);
      }
    }
  }
};

#endif // INCLUDED_TYPED_EXPR
