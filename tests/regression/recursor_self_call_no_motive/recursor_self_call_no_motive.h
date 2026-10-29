#ifndef INCLUDED_RECURSOR_SELF_CALL_NO_MOTIVE
#define INCLUDED_RECURSOR_SELF_CALL_NO_MOTIVE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// The recursive calls of a type-indexed family's recursor.
///
/// expr_rect's C++ template spells its motive T1 only in its result
/// type, so no argument deduces it.  Its recursive calls wrote no template
/// arguments, leaving every one to deduction from the recursive argument,
/// as for a nested inductive, whose self-calls are at another
/// instantiation; but expr's C++ type takes no index, so the header
/// compiled until the recursor was instantiated, and then no call matched.
/// The calls now write the motive.
struct RecursorSelfCallNoMotive {
  struct expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Bl {
      bool a0;
    };

    struct SuccE {
      std::shared_ptr<expr> a0;
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

    struct FstE {
      std::shared_ptr<expr> a;
    };

    using variant_t = std::variant<Lit, Bl, SuccE, Ite, PairE, FstE>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Bl _v) : v_(std::move(_v)) {}

    explicit expr(SuccE _v) : v_(std::move(_v)) {}

    explicit expr(Ite _v) : v_(std::move(_v)) {}

    explicit expr(PairE _v) : v_(std::move(_v)) {}

    explicit expr(FstE _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr bl(bool a0) { return expr(Bl{a0}); }

    static expr succe(expr a0) {
      return expr(SuccE{std::make_shared<expr>(std::move(a0))});
    }

    static expr ite(expr a, expr a1, expr a2) {
      return expr(Ite{std::make_shared<expr>(std::move(a)),
                      std::make_shared<expr>(std::move(a1)),
                      std::make_shared<expr>(std::move(a2))});
    }

    static expr paire(expr a, expr b) {
      return expr(PairE{std::make_shared<expr>(std::move(a)),
                        std::make_shared<expr>(std::move(b))});
    }

    static expr fste(expr a) {
      return expr(FstE{std::make_shared<expr>(std::move(a))});
    }

    // MANIPULATORS
    ~expr() {
      if (std::holds_alternative<Lit>(v_mut())) {
        return;
      }
      if (std::holds_alternative<Bl>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<SuccE>(&v_mut())) {
        if (!(_alt->a0 && _alt->a0.use_count() == 1)) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Ite>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<PairE>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->b && _alt->b.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<FstE>(&v_mut())) {
        if (!(_alt->a && _alt->a.use_count() == 1)) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<SuccE>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
        if (auto *_alt = std::get_if<Ite>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
        if (auto *_alt = std::get_if<PairE>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
          }
          if (_alt->b && _alt->b.use_count() == 1) {
            _stack.push_back(std::move(_alt->b));
          }
        }
        if (auto *_alt = std::get_if<FstE>(&_v)) {
          if (_alt->a && _alt->a.use_count() == 1) {
            _stack.push_back(std::move(_alt->a));
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

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4, typename F5>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      const expr &e) {
    if (std::holds_alternative<typename expr::Lit>(e.v())) {
      const auto &[a0] = std::get<typename expr::Lit>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
      const auto &[a0] = std::get<typename expr::Bl>(e.v());
      return f0(a0);
    } else if (std::holds_alternative<typename expr::SuccE>(e.v())) {
      const auto &[a0] = std::get<typename expr::SuccE>(e.v());
      return f1(*a0, expr_rect<T1>(f, f0, f1, f2, f3, f4, *a0));
    } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
      const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
      return crane_any_cast<T1>(
          f2(*a, expr_rect<T1>(f, f0, f1, f2, f3, f4, *a), *a1,
             expr_rect<T1>(f, f0, f1, f2, f3, f4, *a1), *a2,
             expr_rect<T1>(f, f0, f1, f2, f3, f4, *a2)));
    } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
      const auto &[a, b] = std::get<typename expr::PairE>(e.v());
      return crane_any_cast<T1>(f3(*a, expr_rect<T1>(f, f0, f1, f2, f3, f4, *a),
                                   *b,
                                   expr_rect<T1>(f, f0, f1, f2, f3, f4, *b)));
    } else {
      const auto &[a] = std::get<typename expr::FstE>(e.v());
      return crane_any_cast<T1>(
          f4(*a, expr_rect<T1>(f, f0, f1, f2, f3, f4, *a)));
    }
  }

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4, typename F5>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                     const expr &e) {
    if (std::holds_alternative<typename expr::Lit>(e.v())) {
      const auto &[a0] = std::get<typename expr::Lit>(e.v());
      return f(a0);
    } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
      const auto &[a0] = std::get<typename expr::Bl>(e.v());
      return f0(a0);
    } else if (std::holds_alternative<typename expr::SuccE>(e.v())) {
      const auto &[a0] = std::get<typename expr::SuccE>(e.v());
      return f1(*a0, expr_rec<T1>(f, f0, f1, f2, f3, f4, *a0));
    } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
      const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
      return crane_any_cast<T1>(
          f2(*a, expr_rec<T1>(f, f0, f1, f2, f3, f4, *a), *a1,
             expr_rec<T1>(f, f0, f1, f2, f3, f4, *a1), *a2,
             expr_rec<T1>(f, f0, f1, f2, f3, f4, *a2)));
    } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
      const auto &[a, b] = std::get<typename expr::PairE>(e.v());
      return crane_any_cast<T1>(f3(*a, expr_rec<T1>(f, f0, f1, f2, f3, f4, *a),
                                   *b,
                                   expr_rec<T1>(f, f0, f1, f2, f3, f4, *b)));
    } else {
      const auto &[a] = std::get<typename expr::FstE>(e.v());
      return crane_any_cast<T1>(
          f4(*a, expr_rec<T1>(f, f0, f1, f2, f3, f4, *a)));
    }
  }

  static inline const expr sample = expr::fste(
      expr::paire(expr::succe(expr::lit(UINT64_C(3))), expr::bl(true)));
};

#endif // INCLUDED_RECURSOR_SELF_CALL_NO_MOTIVE
