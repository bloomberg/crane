#ifndef INCLUDED_TYPED_EXPR
#define INCLUDED_TYPED_EXPR

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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
    Ty d_a0;
    std::shared_ptr<Expr> d_a1;
    std::shared_ptr<Expr> d_a2;
    std::shared_ptr<Expr> d_a3;
  };

  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Expr(ENat _v) : d_v_(std::move(_v)) {}

  explicit Expr(EBool _v) : d_v_(std::move(_v)) {}

  explicit Expr(EAdd _v) : d_v_(std::move(_v)) {}

  explicit Expr(EEq _v) : d_v_(std::move(_v)) {}

  explicit Expr(EIf _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Expr> ENat_(unsigned int a0) {
      return std::shared_ptr<Expr>(new Expr(ENat{a0}));
    }

    static std::shared_ptr<Expr> EBool_(bool a0) {
      return std::shared_ptr<Expr>(new Expr(EBool{a0}));
    }

    static std::shared_ptr<Expr> EAdd_(const std::shared_ptr<Expr> &a0,
                                       const std::shared_ptr<Expr> &a1) {
      return std::shared_ptr<Expr>(new Expr(EAdd{a0, a1}));
    }

    static std::shared_ptr<Expr> EEq_(const std::shared_ptr<Expr> &a0,
                                      const std::shared_ptr<Expr> &a1) {
      return std::shared_ptr<Expr>(new Expr(EEq{a0, a1}));
    }

    static std::shared_ptr<Expr> EIf_(Ty a0, const std::shared_ptr<Expr> &a1,
                                      const std::shared_ptr<Expr> &a2,
                                      const std::shared_ptr<Expr> &a3) {
      return std::shared_ptr<Expr>(new Expr(EIf{a0, a1, a2, a3}));
    }

    static std::unique_ptr<Expr> ENat_uptr(unsigned int a0) {
      return std::unique_ptr<Expr>(new Expr(ENat{a0}));
    }

    static std::unique_ptr<Expr> EBool_uptr(bool a0) {
      return std::unique_ptr<Expr>(new Expr(EBool{a0}));
    }

    static std::unique_ptr<Expr> EAdd_uptr(const std::shared_ptr<Expr> &a0,
                                           const std::shared_ptr<Expr> &a1) {
      return std::unique_ptr<Expr>(new Expr(EAdd{a0, a1}));
    }

    static std::unique_ptr<Expr> EEq_uptr(const std::shared_ptr<Expr> &a0,
                                          const std::shared_ptr<Expr> &a1) {
      return std::unique_ptr<Expr>(new Expr(EEq{a0, a1}));
    }

    static std::unique_ptr<Expr> EIf_uptr(Ty a0,
                                          const std::shared_ptr<Expr> &a1,
                                          const std::shared_ptr<Expr> &a2,
                                          const std::shared_ptr<Expr> &a3) {
      return std::unique_ptr<Expr>(new Expr(EIf{a0, a1, a2, a3}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::any eval(const Ty _x) const {
    return std::visit(
        Overloaded{
            [](const typename Expr::ENat _args) -> std::any {
              unsigned int n = _args.d_a0;
              return std::move(n);
            },
            [](const typename Expr::EBool _args) -> std::any {
              bool b = _args.d_a0;
              return std::move(b);
            },
            [](const typename Expr::EAdd _args) -> std::any {
              std::shared_ptr<Expr> a = _args.d_a0;
              std::shared_ptr<Expr> b = _args.d_a1;
              return (
                  std::any_cast<unsigned int>(std::move(a)->eval(Ty::e_TNAT)) +
                  std::any_cast<unsigned int>(std::move(b)->eval(Ty::e_TNAT)));
            },
            [](const typename Expr::EEq _args) -> std::any {
              std::shared_ptr<Expr> a = _args.d_a0;
              std::shared_ptr<Expr> b = _args.d_a1;
              return std::any_cast<unsigned int>(
                         std::move(a)->eval(Ty::e_TNAT)) ==
                     std::any_cast<unsigned int>(
                         std::move(b)->eval(Ty::e_TNAT));
            },
            [](const typename Expr::EIf _args) -> std::any {
              Ty t0 = _args.d_a0;
              std::shared_ptr<Expr> c = _args.d_a1;
              std::shared_ptr<Expr> th = _args.d_a2;
              std::shared_ptr<Expr> el = _args.d_a3;
              if (std::any_cast<bool>(std::move(c)->eval(Ty::e_TBOOL))) {
                return std::move(th)->eval(t0);
              } else {
                return std::move(el)->eval(t0);
              }
            }},
        this->v());
  }
};

#endif // INCLUDED_TYPED_EXPR
