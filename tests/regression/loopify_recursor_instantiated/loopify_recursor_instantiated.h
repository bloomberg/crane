#ifndef INCLUDED_LOOPIFY_RECURSOR_INSTANTIATED
#define INCLUDED_LOOPIFY_RECURSOR_INSTANTIATED

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A recursor of a type-indexed family, loopified and instantiated.
///
/// expr_rect reads its recursive calls through a coercion, at the motive
/// of the index each constructor fixes.  Normalize left them in place,
/// ordinary C++ calls inside the machine, and a call left there names no
/// instantiation: the recursor's C++ spells its motive T1 only in its
/// result type, nothing deduces it (wip/recursor_self_call_no_motive), and
/// size did not compile.  Each is now bound at the motive, which the
/// recursor's C++ spells, and the machine resumes after it: a succE chain
/// a hundred thousand deep runs in one machine.
struct LoopifyRecursorInstantiated {
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

    /// CraneCont_FstE: saves [a], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_FstE {
      std::shared_ptr<expr> a;
    };

    /// CraneCont_Ite: saves [a, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
    };

    /// CraneCont_Ite_1: saves [a, a1, a2, _tmp4], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Ite_1 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
    };

    /// CraneCont_Ite_2: saves [a, a1, a2, _tmp4, _tmp3], resumes after
    /// recursive call, then processes rest.
    struct CraneCont_Ite_2 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
      T1 _tmp3;
    };

    /// CraneCont_PairE: saves [a, b], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_PairE {
      std::shared_ptr<expr> a;
      const expr *b;
    };

    /// CraneCont_PairE_1: saves [a, b, _tmp6], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_PairE_1 {
      std::shared_ptr<expr> a;
      const expr *b;
      T1 _tmp6;
    };

    /// CraneCont_SuccE: saves [a0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_SuccE {
      std::shared_ptr<expr> a0;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_FstE, CraneCont_Ite, CraneCont_Ite_1,
                     CraneCont_Ite_2, CraneCont_PairE, CraneCont_PairE_1,
                     CraneCont_SuccE>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified expr_rect: CraneEnter -> CraneCont_FstE -> CraneCont_Ite ->
    /// CraneCont_Ite_1 -> CraneCont_Ite_2 -> CraneCont_PairE ->
    /// CraneCont_PairE_1 -> CraneCont_SuccE.
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
          _stack.emplace_back(CraneCont_SuccE{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{a, crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _stack.emplace_back(CraneCont_PairE{a, crane_raw(b)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _stack.emplace_back(CraneCont_FstE{a});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        }
      } else if (std::holds_alternative<CraneCont_FstE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_FstE>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        _result = crane_any_cast<T1>(f4(*a, std::move(_result)));
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
            std::move(a), &a1, &a2, std::move(_f._tmp4), std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else if (std::holds_alternative<CraneCont_Ite_2>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite_2>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f2(*a, std::move(_f._tmp4), a1,
                                  std::move(_f._tmp3), a2, std::move(_result)));
      } else if (std::holds_alternative<CraneCont_PairE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _stack.emplace_back(
            CraneCont_PairE_1{std::move(a), &b, std::move(_result)});
        _stack.emplace_back(CraneEnter{&b});
      } else if (std::holds_alternative<CraneCont_PairE_1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE_1>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _result = crane_any_cast<T1>(
            f3(*a, std::move(_f._tmp6), b, std::move(_result)));
      } else {
        auto _f = std::move(std::get<CraneCont_SuccE>(_frame));
        std::shared_ptr<expr> a0 = std::move(_f.a0);
        _result = f1(*a0, std::move(_result));
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

    /// CraneCont_FstE: saves [a], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_FstE {
      std::shared_ptr<expr> a;
    };

    /// CraneCont_Ite: saves [a, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
    };

    /// CraneCont_Ite_1: saves [a, a1, a2, _tmp4], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Ite_1 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
    };

    /// CraneCont_Ite_2: saves [a, a1, a2, _tmp4, _tmp3], resumes after
    /// recursive call, then processes rest.
    struct CraneCont_Ite_2 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
      T1 _tmp3;
    };

    /// CraneCont_PairE: saves [a, b], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_PairE {
      std::shared_ptr<expr> a;
      const expr *b;
    };

    /// CraneCont_PairE_1: saves [a, b, _tmp6], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_PairE_1 {
      std::shared_ptr<expr> a;
      const expr *b;
      T1 _tmp6;
    };

    /// CraneCont_SuccE: saves [a0], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_SuccE {
      std::shared_ptr<expr> a0;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_FstE, CraneCont_Ite, CraneCont_Ite_1,
                     CraneCont_Ite_2, CraneCont_PairE, CraneCont_PairE_1,
                     CraneCont_SuccE>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified expr_rec: CraneEnter -> CraneCont_FstE -> CraneCont_Ite ->
    /// CraneCont_Ite_1 -> CraneCont_Ite_2 -> CraneCont_PairE ->
    /// CraneCont_PairE_1 -> CraneCont_SuccE.
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
          _stack.emplace_back(CraneCont_SuccE{a0});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{a, crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _stack.emplace_back(CraneCont_PairE{a, crane_raw(b)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _stack.emplace_back(CraneCont_FstE{a});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        }
      } else if (std::holds_alternative<CraneCont_FstE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_FstE>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        _result = crane_any_cast<T1>(f4(*a, std::move(_result)));
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
            std::move(a), &a1, &a2, std::move(_f._tmp4), std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else if (std::holds_alternative<CraneCont_Ite_2>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite_2>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f2(*a, std::move(_f._tmp4), a1,
                                  std::move(_f._tmp3), a2, std::move(_result)));
      } else if (std::holds_alternative<CraneCont_PairE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _stack.emplace_back(
            CraneCont_PairE_1{std::move(a), &b, std::move(_result)});
        _stack.emplace_back(CraneEnter{&b});
      } else if (std::holds_alternative<CraneCont_PairE_1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE_1>(_frame));
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _result = crane_any_cast<T1>(
            f3(*a, std::move(_f._tmp6), b, std::move(_result)));
      } else {
        auto _f = std::move(std::get<CraneCont_SuccE>(_frame));
        std::shared_ptr<expr> a0 = std::move(_f.a0);
        _result = f1(*a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1 = void>
  static uint64_t size(const expr &e) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const expr *e;
    };

    /// CraneCont_FstE: resumes after recursive call, then processes rest.
    struct CraneCont_FstE {};

    /// CraneCont_Ite: saves [a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite {
      const expr *a1;
      const expr *a2;
    };

    /// CraneCont_Ite_1: saves [a2, _tmp4], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Ite_1 {
      const expr *a2;
      uint64_t _tmp4;
    };

    /// CraneCont_Ite_2: saves [_tmp4, _tmp3], resumes after recursive call,
    /// then processes rest.
    struct CraneCont_Ite_2 {
      uint64_t _tmp4;
      uint64_t _tmp3;
    };

    /// CraneCont_PairE: saves [b], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_PairE {
      const expr *b;
    };

    /// CraneCont_PairE_1: saves [_tmp6], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_PairE_1 {
      uint64_t _tmp6;
    };

    /// CraneCont_SuccE: resumes after recursive call, then processes rest.
    struct CraneCont_SuccE {};

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_FstE, CraneCont_Ite, CraneCont_Ite_1,
                     CraneCont_Ite_2, CraneCont_PairE, CraneCont_PairE_1,
                     CraneCont_SuccE>;
    uint64_t _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified size: CraneEnter -> CraneCont_FstE -> CraneCont_Ite ->
    /// CraneCont_Ite_1 -> CraneCont_Ite_2 -> CraneCont_PairE ->
    /// CraneCont_PairE_1 -> CraneCont_SuccE.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const expr &e = *_f.e;
        if (std::holds_alternative<typename expr::SuccE>(e.v())) {
          const auto &[a0] = std::get<typename expr::SuccE>(e.v());
          _stack.emplace_back(CraneCont_SuccE{});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(CraneCont_Ite{crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _stack.emplace_back(CraneCont_PairE{crane_raw(b)});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::FstE>(e.v())) {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _stack.emplace_back(CraneCont_FstE{});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        } else {
          _result = UINT64_C(1);
        }
      } else if (std::holds_alternative<CraneCont_FstE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_FstE>(_frame));
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<CraneCont_Ite>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite>(_frame));
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Ite_1{&a2, std::move(_result)});
        _stack.emplace_back(CraneEnter{&a1});
      } else if (std::holds_alternative<CraneCont_Ite_1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite_1>(_frame));
        const expr &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Ite_2{_f._tmp4, std::move(_result)});
        _stack.emplace_back(CraneEnter{&a2});
      } else if (std::holds_alternative<CraneCont_Ite_2>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite_2>(_frame));
        _result = (((_f._tmp4 + _f._tmp3) + std::move(_result)) + 1);
      } else if (std::holds_alternative<CraneCont_PairE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE>(_frame));
        const expr &b = *_f.b;
        _stack.emplace_back(CraneCont_PairE_1{std::move(_result)});
        _stack.emplace_back(CraneEnter{&b});
      } else if (std::holds_alternative<CraneCont_PairE_1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE_1>(_frame));
        _result = ((_f._tmp6 + std::move(_result)) + 1);
      } else {
        auto _f = std::move(std::get<CraneCont_SuccE>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  static inline const expr sample = expr::fste(
      expr::paire(expr::succe(expr::lit(UINT64_C(3))), expr::bl(true)));

  static inline const uint64_t run = size<uint64_t>(sample);
};

#endif // INCLUDED_LOOPIFY_RECURSOR_INSTANTIATED
