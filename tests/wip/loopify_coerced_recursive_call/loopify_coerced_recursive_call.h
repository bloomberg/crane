#ifndef INCLUDED_LOOPIFY_COERCED_RECURSIVE_CALL
#define INCLUDED_LOOPIFY_COERCED_RECURSIVE_CALL

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Recursive calls under a coercion, in a function Loopify lowers to a
/// machine with a stack of frames.
///
/// A type-indexed evaluator reads a recursive result at the type its
/// branch gives it, through a coercion: S (eval x), (eval x, eval y),
/// fst (eval p).  Normalize binds every recursive call that is not a
/// tail call, so that the machine resumes after it, but touches nothing
/// under a coercion (only a call matched through one, if eval c).  The
/// calls above stay ordinary C++ calls inside eval's machine, each
/// running a machine of its own, and a succE chain a hundred thousand
/// deep exhausts the stack.  Binding them needs a temporary whose C++ type
/// the coercion can still cast from: typed at the call's instantiated type,
/// or at the coercion's source type, the coercion is dropped
/// (_result.first on a crane::obj).
///
/// Expected: stack overflow in eval.  When fixed: prints ok.
struct LoopifyCoercedRecursiveCall {
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
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4, typename F5>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                      const expr &e) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const expr *e;
    };

    /// CraneCont_Ite: saves [a, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> a1;
      const expr *a2;
    };

    /// CraneCont_Ite_1: saves [a, a1, a2, _tmp2], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Ite_1 {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> a1;
      const expr *a2;
      T1 _tmp2;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Ite, CraneCont_Ite_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified expr_rect: CraneEnter -> CraneCont_Ite -> CraneCont_Ite_1.
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
        } else if (std::holds_alternative<typename expr::SuccE>(e.v())) {
          const auto &[a0] = std::get<typename expr::SuccE>(e.v());
          _result = f1(*a0, expr_rect(f, f0, f1, f2, f3, f4, *a0));
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{a, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _result =
              crane_any_cast<T1>(f3(*a, expr_rect(f, f0, f1, f2, f3, f4, *a),
                                    *b, expr_rect(f, f0, f1, f2, f3, f4, *b)));
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _result =
              crane_any_cast<T1>(f4(*a, expr_rect(f, f0, f1, f2, f3, f4, *a)));
        }
      } else if (std::holds_alternative<CraneCont_Ite>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        std::shared_ptr<expr> a1 = std::move(_f.a1);
        const expr &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Ite_1{std::move(a), std::move(a1), &a2,
                                            std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Ite_1>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        std::shared_ptr<expr> a1 = std::move(_f.a1);
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f2(*a, expr_rect(f, f0, f1, f2, f3, f4, *a), *a1,
                                  std::move(_f._tmp2), a2, std::move(_result)));
      }
    }
    return _result;
  }

  template <typename T1, typename T2 = void, typename F0, typename F1,
            typename F2, typename F3, typename F4, typename F5>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, const bool &>
  static T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1, F3 &&f2, F4 &&f3, F5 &&f4,
                     const expr &e) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const expr *e;
    };

    /// CraneCont_Ite: saves [a, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> a1;
      const expr *a2;
    };

    /// CraneCont_Ite_1: saves [a, a1, a2, _tmp2], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Ite_1 {
      std::shared_ptr<expr> a;
      std::shared_ptr<expr> a1;
      const expr *a2;
      T1 _tmp2;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Ite, CraneCont_Ite_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified expr_rec: CraneEnter -> CraneCont_Ite -> CraneCont_Ite_1.
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
        } else if (std::holds_alternative<typename expr::SuccE>(e.v())) {
          const auto &[a0] = std::get<typename expr::SuccE>(e.v());
          _result = f1(*a0, expr_rec(f, f0, f1, f2, f3, f4, *a0));
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{a, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _result =
              crane_any_cast<T1>(f3(*a, expr_rec(f, f0, f1, f2, f3, f4, *a), *b,
                                    expr_rec(f, f0, f1, f2, f3, f4, *b)));
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _result =
              crane_any_cast<T1>(f4(*a, expr_rec(f, f0, f1, f2, f3, f4, *a)));
        }
      } else if (std::holds_alternative<CraneCont_Ite>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        std::shared_ptr<expr> a1 = std::move(_f.a1);
        const expr &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Ite_1{std::move(a), std::move(a1), &a2,
                                            std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Ite_1>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        std::shared_ptr<expr> a1 = std::move(_f.a1);
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f2(*a, expr_rec(f, f0, f1, f2, f3, f4, *a), *a1,
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

    /// CraneCont_Ite: saves [a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      const expr *a1;
      const expr *a2;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Ite>;
    crane::obj _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified eval: CraneEnter -> CraneCont_Ite.
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
        } else if (std::holds_alternative<typename expr::SuccE>(e.v())) {
          const auto &[a0] = std::get<typename expr::SuccE>(e.v());
          _result = (crane::any_cast<uint64_t>(eval<crane::obj>(*a0)) + 1);
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _result = std::make_pair(crane::obj(eval<crane::obj>(*a)),
                                   crane::obj(eval<crane::obj>(*b)));
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _result = crane_any_cast<std::pair<crane::obj, crane::obj>>(
                        eval<crane::obj>(*a))
                        .first;
        }
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

  static inline const expr sample = expr::fste(
      expr::paire(expr::succe(expr::lit(UINT64_C(3))), expr::bl(true)));

  static inline const uint64_t run =
      crane::any_cast<uint64_t>(eval<uint64_t>(sample));
};

#endif // INCLUDED_LOOPIFY_COERCED_RECURSIVE_CALL
