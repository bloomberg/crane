#ifndef INCLUDED_LOOPIFY_COERCED_SCRUTINEE
#define INCLUDED_LOOPIFY_COERCED_SCRUTINEE

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// A recursive call matched through a coercion is bound before the match,
/// as one matched directly is.
///
/// In a type-indexed evaluator if eval c then ... reads the call through a
/// coercion to bool, since eval returns its index erased.  Normalize left
/// anything under a coercion where it stood, so the plan had no point to
/// resume at, and Loopify bound the call itself, in a variable the plan knew
/// nothing of.  Normalize now binds it; the continuation casts the result of
/// the call it re-enters by.
struct LoopifyCoercedScrutinee {
  struct expr {
    // TYPES
    struct Lit {
      uint64_t a0;
    };

    struct Bl {
      bool a0;
    };

    struct Ite {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> a1;
      std::shared_ptr<expr> a2;
    };

    struct Iszero {
      std::shared_ptr<expr> a0;
    };

    using variant_t = std::variant<Lit, Bl, Ite, Iszero>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Bl _v) : v_(std::move(_v)) {}

    explicit expr(Ite _v) : v_(std::move(_v)) {}

    explicit expr(Iszero _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr bl(bool a0) { return expr(Bl{a0}); }

    static expr ite(expr a, expr a1, expr a2) {
      return expr(Ite{std::make_shared<expr>(std::move(a)),
                      std::make_shared<expr>(std::move(a1)),
                      std::make_shared<expr>(std::move(a2))});
    }

    static expr iszero(expr a0) {
      return expr(Iszero{std::make_shared<expr>(std::move(a0))});
    }

    // MANIPULATORS
    ~expr() {
      if (std::holds_alternative<Lit>(v_mut())) {
        return;
      }
      if (std::holds_alternative<Bl>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Ite>(&v_mut())) {
        if (!((_alt->a && _alt->a.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Iszero>(&v_mut())) {
        if (!(_alt->a0 && _alt->a0.use_count() == 1)) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
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
        if (auto *_alt = std::get_if<Iszero>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
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

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2,
                      const expr &e) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const expr *e;
    };

    /// CraneCont_Iszero: saves [a0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Iszero {
      std::shared_ptr<expr> a0;
    };

    /// CraneCont_Ite: saves [a, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
    };

    /// CraneCont_Ite_1: saves [a, a1, a2, _tmp3], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Ite_1 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp3;
    };

    /// CraneCont_Ite_2: saves [a, a1, a2, _tmp3, _tmp2], resumes after
    /// recursive call, then processes rest.
    struct CraneCont_Ite_2 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp3;
      T1 _tmp2;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Iszero, CraneCont_Ite,
                                    CraneCont_Ite_1, CraneCont_Ite_2>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified expr_rect: CraneEnter -> CraneCont_Iszero -> CraneCont_Ite ->
    /// CraneCont_Ite_1 -> CraneCont_Ite_2.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const expr &e = *_f.e;
        if (std::holds_alternative<typename expr::Lit>(e.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(e.v());
          _result = f(a0);
        } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
          const auto &[a0] = std::get<typename expr::Bl>(e.v());
          _result = f0(a0);
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{a, crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else {
          const auto &[a0] = std::get<typename expr::Iszero>(e.v());
          _stack.emplace_back(CraneCont_Iszero{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Iszero>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Iszero>(_frame));
        std::shared_ptr<expr> a0 = std::move(_f.a0);
        _result = f2(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_Ite>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Ite_1{std::move(a), &a1, &a2, std::move(_result)});
        _stack.emplace_back(CraneEnter{&a1});
      } else if (std::holds_alternative<CraneCont_Ite_1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite_1>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Ite_2{
            std::move(a), &a1, &a2, std::move(_f._tmp3), std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Ite_2>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f1(*a, std::move(_f._tmp3), a1,
                                  std::move(_f._tmp2), a2, std::move(_result)));
      }
    }
    return _result;
  }

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2,
                     const expr &e) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const expr *e;
    };

    /// CraneCont_Iszero: saves [a0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Iszero {
      std::shared_ptr<expr> a0;
    };

    /// CraneCont_Ite: saves [a, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
    };

    /// CraneCont_Ite_1: saves [a, a1, a2, _tmp3], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Ite_1 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp3;
    };

    /// CraneCont_Ite_2: saves [a, a1, a2, _tmp3, _tmp2], resumes after
    /// recursive call, then processes rest.
    struct CraneCont_Ite_2 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp3;
      T1 _tmp2;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Iszero, CraneCont_Ite,
                                    CraneCont_Ite_1, CraneCont_Ite_2>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified expr_rec: CraneEnter -> CraneCont_Iszero -> CraneCont_Ite ->
    /// CraneCont_Ite_1 -> CraneCont_Ite_2.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const expr &e = *_f.e;
        if (std::holds_alternative<typename expr::Lit>(e.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(e.v());
          _result = f(a0);
        } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
          const auto &[a0] = std::get<typename expr::Bl>(e.v());
          _result = f0(a0);
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{a, crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else {
          const auto &[a0] = std::get<typename expr::Iszero>(e.v());
          _stack.emplace_back(CraneCont_Iszero{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Iszero>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Iszero>(_frame));
        std::shared_ptr<expr> a0 = std::move(_f.a0);
        _result = f2(*a0, std::move(_result));
      } else if (std::holds_alternative<CraneCont_Ite>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Ite_1{std::move(a), &a1, &a2, std::move(_result)});
        _stack.emplace_back(CraneEnter{&a1});
      } else if (std::holds_alternative<CraneCont_Ite_1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite_1>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Ite_2{
            std::move(a), &a1, &a2, std::move(_f._tmp3), std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Ite_2>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f1(*a, std::move(_f._tmp3), a1,
                                  std::move(_f._tmp2), a2, std::move(_result)));
      }
    }
    return _result;
  }

  template <typename T1 = void>
  static crane::obj
  eval(const expr &e) { /// CraneEnter: captures varying parameters for each
                        /// recursive call.

    struct CraneEnter {
      const expr *e;
    };

    /// CraneCont_Iszero: resumes after recursive call, then processes rest.
    struct CraneCont_Iszero {};

    /// CraneCont_Ite: saves [a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      const expr *a1;
      const expr *a2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Iszero, CraneCont_Ite>;
    crane::obj _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified eval: CraneEnter -> CraneCont_Iszero -> CraneCont_Ite.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const expr &e = *_f.e;
        if (std::holds_alternative<typename expr::Lit>(e.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(e.v());
          _result = std::move(a0);
        } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
          const auto &[a0] = std::get<typename expr::Bl>(e.v());
          _result = std::move(a0);
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else {
          const auto &[a0] = std::get<typename expr::Iszero>(e.v());
          _stack.emplace_back(CraneCont_Iszero{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Iszero>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Iszero>(_frame));
        _result = crane::any_cast<uint64_t>(std::move(_result)) == UINT64_C(0);
      } else {
        auto _f = std::move(std::get<CraneCont_Ite>(_frame));
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        if (crane::any_cast<bool>(std::move(_result))) {
          _stack.emplace_back(CraneEnter{&a1});
        } else {
          _stack.emplace_back(CraneEnter{&a2});
        }
      }
    }
    return _result;
  }

  /// n conditionals, each taking its else branch until the innermost.
  static expr nest(uint64_t n);
  static inline const uint64_t deep =
      crane::any_cast<uint64_t>(eval<uint64_t>(nest(UINT64_C(50))));

  static inline const uint64_t chosen =
      crane::any_cast<uint64_t>(eval<uint64_t>(
          expr::ite(expr::ite(expr::bl(false), expr::bl(false),
                              expr::iszero(expr::lit(UINT64_C(0)))),
                    expr::lit(UINT64_C(3)), expr::lit(UINT64_C(4)))));
};

#endif // INCLUDED_LOOPIFY_COERCED_SCRUTINEE
