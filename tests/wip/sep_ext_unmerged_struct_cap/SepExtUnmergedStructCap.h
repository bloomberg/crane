#ifndef INCLUDED_SEPEXTUNMERGEDSTRUCTCAP
#define INCLUDED_SEPEXTUNMERGEDSTRUCTCAP

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
