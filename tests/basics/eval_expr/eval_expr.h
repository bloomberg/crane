#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class ty { TNat, TBool };

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
      ty _a0;
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
      EIf_(ty a0, const std::shared_ptr<Expr::expr> &a1,
           const std::shared_ptr<Expr::expr> &a2,
           const std::shared_ptr<Expr::expr> &a3) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EIf{a0, a1, a2, a3}));
      }
      static std::unique_ptr<Expr::expr> ENat_uptr(unsigned int a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(ENat{a0}));
      }
      static std::unique_ptr<Expr::expr> EBool_uptr(bool a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(EBool{a0}));
      }
      static std::unique_ptr<Expr::expr>
      EAdd_uptr(const std::shared_ptr<Expr::expr> &a0,
                const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(EAdd{a0, a1}));
      }
      static std::unique_ptr<Expr::expr>
      EEq_uptr(const std::shared_ptr<Expr::expr> &a0,
               const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(EEq{a0, a1}));
      }
      static std::unique_ptr<Expr::expr>
      EIf_uptr(ty a0, const std::shared_ptr<Expr::expr> &a1,
               const std::shared_ptr<Expr::expr> &a2,
               const std::shared_ptr<Expr::expr> &a3) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(EIf{a0, a1, a2, a3}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    std::any eval(const ty _x) const {
      return std::visit(
          Overloaded{
              [](const typename Expr::expr::ENat _args) -> std::any {
                unsigned int n = _args._a0;
                return std::move(n);
              },
              [](const typename Expr::expr::EBool _args) -> std::any {
                bool b = _args._a0;
                return std::move(b);
              },
              [](const typename Expr::expr::EAdd _args) -> std::any {
                std::shared_ptr<Expr::expr> a = _args._a0;
                std::shared_ptr<Expr::expr> b = _args._a1;
                return (
                    std::any_cast<unsigned int>(std::move(a)->eval(ty::TNat)) +
                    std::any_cast<unsigned int>(std::move(b)->eval(ty::TNat)));
              },
              [](const typename Expr::expr::EEq _args) -> std::any {
                std::shared_ptr<Expr::expr> a = _args._a0;
                std::shared_ptr<Expr::expr> b = _args._a1;
                return (
                    std::any_cast<unsigned int>(std::move(a)->eval(ty::TNat)) ==
                    std::any_cast<unsigned int>(std::move(b)->eval(ty::TNat)));
              },
              [](const typename Expr::expr::EIf _args) -> std::any {
                ty t0 = _args._a0;
                std::shared_ptr<Expr::expr> c = _args._a1;
                std::shared_ptr<Expr::expr> th = _args._a2;
                std::shared_ptr<Expr::expr> el = _args._a3;
                if (std::any_cast<bool>(c->eval(ty::TBool))) {
                  return std::move(th)->eval(t0);
                } else {
                  return std::move(el)->eval(t0);
                }
              }},
          this->v());
    }
  };
};
