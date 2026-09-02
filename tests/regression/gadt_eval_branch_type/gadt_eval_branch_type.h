#ifndef INCLUDED_GADT_EVAL_BRANCH_TYPE
#define INCLUDED_GADT_EVAL_BRANCH_TYPE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct GadtEvalBranchType {
  /// A type-indexed expr evaluated recursively.  Each branch of eval has a
  /// different result type, so no single C++ return type serves them all: the
  /// result is erased to std::any and recovered at each use.
  struct expr {
    // TYPES
    struct Lit {
      Nat a0;
    };

    struct Bl {
      bool a0;
    };

    struct Ite {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
    };

    struct PairE {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> b;
    };

    using variant_t = std::variant<Lit, Bl, Ite, PairE>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Bl _v) : v_(std::move(_v)) {}

    explicit expr(Ite _v) : v_(std::move(_v)) {}

    explicit expr(PairE _v) : v_(std::move(_v)) {}

    static expr lit(Nat a0) { return expr(Lit{std::move(a0)}); }

    static expr bl(bool a0) { return expr(Bl{a0}); }

    static expr ite(expr a, expr a1, expr a2) {
      return expr(Ite{std::make_shared<expr>(std::move(a)),
                      std::make_shared<expr>(std::move(a1)),
                      std::make_shared<expr>(std::move(a2))});
    }

    static expr paire(expr a, expr b) {
      return expr(PairE{std::make_shared<expr>(std::move(a)),
                        std::make_shared<expr>(std::move(b))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1> static std::any eval(const expr &e) {
    if (std::holds_alternative<typename expr::Lit>(e.v())) {
      const auto &[a0] = std::get<typename expr::Lit>(e.v());
      return a0;
    } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
      const auto &[a0] = std::get<typename expr::Bl>(e.v());
      return a0;
    } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
      const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
      if (std::any_cast<bool>(eval<T1>(*a))) {
        return eval<T1>(*a1);
      } else {
        return eval<T1>(*a2);
      }
    } else {
      const auto &[a, b] = std::get<typename expr::PairE>(e.v());
      return std::make_pair(std::any(eval<T1>(*a)), std::any(eval<T1>(*b)));
    }
  }

  static inline const std::pair<Nat, bool> run =
      crane_any_cast<std::pair<Nat, bool>>(
          eval<std::pair<Nat, bool>>(expr::paire(
              expr::lit(Nat::s(Nat::s(Nat::s(Nat::o())))), expr::bl(true))));
};

#endif // INCLUDED_GADT_EVAL_BRANCH_TYPE
