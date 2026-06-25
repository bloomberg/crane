#ifndef INCLUDED_SEPEXTUNMERGEDSTRUCTCAP
#define INCLUDED_SEPEXTUNMERGEDSTRUCTCAP

#include <memory>
#include <utility>
#include <variant>
#include <vector>

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
      std::vector<std::shared_ptr<Expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Neg>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
        }
      }
    }

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };
};

struct UseExprs {
  static Exprs::Expr make_neg(Exprs::Expr e);
};

} // namespace SepExtUnmergedStructCap

#endif // INCLUDED_SEPEXTUNMERGEDSTRUCTCAP
