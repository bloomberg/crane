#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Ty {
  struct ty {
  public:
    struct TNat {};
    struct TBool {};
    using variant_t = std::variant<TNat, TBool>;

  private:
    variant_t v_;
    explicit ty(TNat _v) : v_(std::move(_v)) {}
    explicit ty(TBool _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Ty::ty> TNat_() {
        return std::shared_ptr<Ty::ty>(new Ty::ty(TNat{}));
      }
      static std::shared_ptr<Ty::ty> TBool_() {
        return std::shared_ptr<Ty::ty>(new Ty::ty(TBool{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Expr {
  struct expr {
  public:
    struct ENat {
      unsigned int _a0;
    };
    struct EBool {
      bool _a0;
    };
    struct EAdd {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct EEq {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct EIf {
      std::shared_ptr<Ty::ty> _a0;
      std::shared_ptr<Expr::expr> _a1;
      std::shared_ptr<Expr::expr> _a2;
      std::shared_ptr<Expr::expr> _a3;
    };
    using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

  private:
    variant_t v_;
    explicit expr(ENat _v) : v_(std::move(_v)) {}
    explicit expr(EBool _v) : v_(std::move(_v)) {}
    explicit expr(EAdd _v) : v_(std::move(_v)) {}
    explicit expr(EEq _v) : v_(std::move(_v)) {}
    explicit expr(EIf _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Expr::expr> ENat_(unsigned int a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(ENat{a0}));
      }
      static std::shared_ptr<Expr::expr> EBool_(bool a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EBool{a0}));
      }
      static std::shared_ptr<Expr::expr>
      EAdd_(const std::shared_ptr<Expr::expr> &a0,
            const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EAdd{a0, a1}));
      }
      static std::shared_ptr<Expr::expr>
      EEq_(const std::shared_ptr<Expr::expr> &a0,
           const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EEq{a0, a1}));
      }
      static std::shared_ptr<Expr::expr>
      EIf_(const std::shared_ptr<Ty::ty> &a0,
           const std::shared_ptr<Expr::expr> &a1,
           const std::shared_ptr<Expr::expr> &a2,
           const std::shared_ptr<Expr::expr> &a3) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EIf{a0, a1, a2, a3}));
      }
    };
    const variant_t &v() const { return v_; }
    std::any eval(const std::shared_ptr<Ty::ty> &_x) const {
      return std::visit(
          Overloaded{[](const typename Expr::expr::ENat _args) -> std::any {
                       unsigned int n = _args._a0;
                       return n;
                     },
                     [](const typename Expr::expr::EBool _args) -> std::any {
                       bool b = _args._a0;
                       return b;
                     },
                     [](const typename Expr::expr::EAdd _args) -> std::any {
                       std::shared_ptr<Expr::expr> a = _args._a0;
                       std::shared_ptr<Expr::expr> b = _args._a1;
                       return (std::any_cast<unsigned int>(
                                   a->eval(Ty::ty::ctor::TNat_())) +
                               std::any_cast<unsigned int>(
                                   b->eval(Ty::ty::ctor::TNat_())));
                     },
                     [](const typename Expr::expr::EEq _args) -> std::any {
                       std::shared_ptr<Expr::expr> a = _args._a0;
                       std::shared_ptr<Expr::expr> b = _args._a1;
                       return (std::any_cast<unsigned int>(
                                   a->eval(Ty::ty::ctor::TNat_())) ==
                               std::any_cast<unsigned int>(
                                   b->eval(Ty::ty::ctor::TNat_())));
                     },
                     [](const typename Expr::expr::EIf _args) -> std::any {
                       std::shared_ptr<Ty::ty> t0 = _args._a0;
                       std::shared_ptr<Expr::expr> c = _args._a1;
                       std::shared_ptr<Expr::expr> th = _args._a2;
                       std::shared_ptr<Expr::expr> el = _args._a3;
                       if (std::any_cast<bool>(
                               c->eval(Ty::ty::ctor::TBool_()))) {
                         return th->eval(t0);
                       } else {
                         return el->eval(t0);
                       }
                     }},
          this->v());
    }
  };
};
