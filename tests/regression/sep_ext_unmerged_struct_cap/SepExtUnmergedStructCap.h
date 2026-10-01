#ifndef INCLUDED_SEPEXTUNMERGEDSTRUCTCAP
#define INCLUDED_SEPEXTUNMERGEDSTRUCTCAP

#include <atomic>
#include <memory>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SepExtUnmergedStructCap {

struct Exprs {
  struct Expr {
    // TYPES
    struct Lit {
      Datatypes::Nat a0;
    };

    struct Neg {
      std::shared_ptr<Expr> a0;
    };

    using variant_t = std::variant<Lit, Neg>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Expr() {}

    explicit Expr(Lit _v) : v_(std::move(_v)) {}

    explicit Expr(Neg _v) : v_(std::move(_v)) {}

    static Expr lit(Datatypes::Nat a0) { return Expr(Lit{std::move(a0)}); }

    static Expr neg(Expr a0) {
      return Expr(Neg{std::make_shared<Expr>(std::move(a0))});
    }

    // MANIPULATORS
    ~Expr() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<Expr> {
        if (auto *_alt = std::get_if<Neg>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<Expr> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    Expr(const Expr &) = default;
    Expr &operator=(const Expr &) = default;
    Expr(Expr &&) noexcept = default;
    Expr &operator=(Expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };
};

struct UseExprs {
  static Exprs::Expr make_neg(const Exprs::Expr &e);
};

} // namespace SepExtUnmergedStructCap

#endif // INCLUDED_SEPEXTUNMERGEDSTRUCTCAP
