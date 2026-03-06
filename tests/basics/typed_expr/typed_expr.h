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

enum class ty { TNat, TBool };

struct Expr {
public:
  struct ENat {
    unsigned int _a0;
  };
  struct EBool {
    bool _a0;
  };
  struct EAdd {
    std::shared_ptr<Expr> _a0;
    std::shared_ptr<Expr> _a1;
  };
  struct EEq {
    std::shared_ptr<Expr> _a0;
    std::shared_ptr<Expr> _a1;
  };
  struct EIf {
    ty _a0;
    std::shared_ptr<Expr> _a1;
    std::shared_ptr<Expr> _a2;
    std::shared_ptr<Expr> _a3;
  };
  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  variant_t v_;
  explicit Expr(ENat _v) : v_(std::move(_v)) {}
  explicit Expr(EBool _v) : v_(std::move(_v)) {}
  explicit Expr(EAdd _v) : v_(std::move(_v)) {}
  explicit Expr(EEq _v) : v_(std::move(_v)) {}
  explicit Expr(EIf _v) : v_(std::move(_v)) {}

public:
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
    static std::shared_ptr<Expr> EIf_(ty a0, const std::shared_ptr<Expr> &a1,
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
    static std::unique_ptr<Expr> EIf_uptr(ty a0,
                                          const std::shared_ptr<Expr> &a1,
                                          const std::shared_ptr<Expr> &a2,
                                          const std::shared_ptr<Expr> &a3) {
      return std::unique_ptr<Expr>(new Expr(EIf{a0, a1, a2, a3}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  std::any eval(const ty _x) const {
    return std::visit(
        Overloaded{
            [](const typename Expr::ENat _args) -> std::any {
              unsigned int n = _args._a0;
              return std::move(n);
            },
            [](const typename Expr::EBool _args) -> std::any {
              bool b = _args._a0;
              return std::move(b);
            },
            [](const typename Expr::EAdd _args) -> std::any {
              std::shared_ptr<Expr> a = _args._a0;
              std::shared_ptr<Expr> b = _args._a1;
              return (
                  std::any_cast<unsigned int>(std::move(a)->eval(ty::TNat)) +
                  std::any_cast<unsigned int>(std::move(b)->eval(ty::TNat)));
            },
            [](const typename Expr::EEq _args) -> std::any {
              std::shared_ptr<Expr> a = _args._a0;
              std::shared_ptr<Expr> b = _args._a1;
              return (
                  std::any_cast<unsigned int>(std::move(a)->eval(ty::TNat)) ==
                  std::any_cast<unsigned int>(std::move(b)->eval(ty::TNat)));
            },
            [](const typename Expr::EIf _args) -> std::any {
              ty t0 = _args._a0;
              std::shared_ptr<Expr> c = _args._a1;
              std::shared_ptr<Expr> th = _args._a2;
              std::shared_ptr<Expr> el = _args._a3;
              if (std::any_cast<bool>(c->eval(ty::TBool))) {
                return std::move(th)->eval(t0);
              } else {
                return std::move(el)->eval(t0);
              }
            }},
        this->v());
  }
};
