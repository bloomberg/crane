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
      std::unique_ptr<Expr> a0;
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

    Expr(const Expr &_other) : v_(std::move(_other.clone().v_)) {}

    Expr(Expr &&_other) : v_(std::move(_other.v_)) {}

    Expr &operator=(const Expr &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    Expr &operator=(Expr &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    Expr clone() const {
      Expr _out{};

      struct _CloneFrame {
        const Expr *_src;
        Expr *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const Expr *_src = _frame._src;
        Expr *_dst = _frame._dst;
        if (std::holds_alternative<Lit>(_src->v())) {
          const auto &_alt = std::get<Lit>(_src->v());
          _dst->v_ = Lit{_alt.a0.clone()};
        } else {
          const auto &_alt = std::get<Neg>(_src->v());
          _dst->v_ = Neg{_alt.a0 ? std::make_unique<Expr>() : nullptr};
          auto &_dst_alt = std::get<Neg>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static Expr lit(Datatypes::Nat a0) { return Expr(Lit{std::move(a0)}); }

    static Expr neg(Expr a0) {
      return Expr(Neg{std::make_unique<Expr>(std::move(a0))});
    }

    // MANIPULATORS
    ~Expr() {
      std::vector<std::unique_ptr<Expr>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](Expr &_node) {
        if (std::holds_alternative<Neg>(_node.v_)) {
          auto &_alt = std::get<Neg>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
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
