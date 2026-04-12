#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include <any>
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
    return std::visit(
        Overloaded{
            [](const typename Expr::ENat &_args) -> std::any {
              return _args.d_a0;
            },
            [](const typename Expr::EBool &_args) -> std::any {
              return _args.d_a0;
            },
            [](const typename Expr::EAdd &_args) -> std::any {
              return (
                  std::any_cast<unsigned int>(_args.d_a0->eval(Ty::e_TNAT)) +
                  std::any_cast<unsigned int>(_args.d_a1->eval(Ty::e_TNAT)));
            },
            [](const typename Expr::EEq &_args) -> std::any {
              return std::any_cast<unsigned int>(
                         _args.d_a0->eval(Ty::e_TNAT)) ==
                     std::any_cast<unsigned int>(_args.d_a1->eval(Ty::e_TNAT));
            },
            [](const typename Expr::EIf &_args) -> std::any {
              if (std::any_cast<bool>(_args.d_a1->eval(Ty::e_TBOOL))) {
                return _args.d_a2->eval(_args.d_t);
              } else {
                return _args.d_a3->eval(_args.d_t);
              }
            }},
        this->v());
  }
};

#endif // INCLUDED_TYPED_EXPR
