#ifndef INCLUDED_LOOPIFY_EXISTENTIAL_RECURSIVE_CALL
#define INCLUDED_LOOPIFY_EXISTENTIAL_RECURSIVE_CALL

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Recursive calls at a constructor's existential types, read at the
/// function's own result type, in a function Loopify lowers to a machine
/// with a stack of frames.
///
/// In (eval x, eval y) each call is at a type pairE hides, which no
/// C++ type spells, so only the box eval returns can hold its value.
/// The pair reads it at eval's own result type A, and translation read
/// a boxed temporary at A by casting it to eval's template parameter,
/// which in a machine is the outermost call's: a bool component would
/// have been cast to the nat of the whole.  So Normalize left these calls
/// in place, ordinary C++ calls inside eval's machine, and a
/// fstE/pairE nest a hundred thousand deep exhausted the stack.  Such a
/// temporary now stays the box, and the calls are bound and resumed like
/// any other.  (fst (eval p) reads its call through a coercion into a
/// pair: see regression/loopify_coerced_recursive_call.)
struct LoopifyExistentialRecursiveCall {
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
  static crane::obj
  eval(const expr &e) { /// CraneEnter: captures varying parameters for each
                        /// recursive call.

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

    /// CraneCont_PairE: saves [b], resumes after recursive call, then processes
    /// rest.
    struct CraneCont_PairE {
      const expr *b;
    };

    /// CraneCont_PairE_1: saves [_tmp4], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_PairE_1 {
      crane::obj _tmp4;
    };

    /// CraneCont_SuccE: resumes after recursive call, then processes rest.
    struct CraneCont_SuccE {};

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_FstE, CraneCont_Ite, CraneCont_PairE,
                     CraneCont_PairE_1, CraneCont_SuccE>;
    crane::obj _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&e});
    /// Loopified eval: CraneEnter -> CraneCont_FstE -> CraneCont_Ite ->
    /// CraneCont_PairE -> CraneCont_PairE_1 -> CraneCont_SuccE.
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
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _stack.emplace_back(CraneCont_FstE{});
          _stack.emplace_back(CraneEnter{crane_raw(a)});
        }
      } else if (std::holds_alternative<CraneCont_FstE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_FstE>(_frame));
        _result = crane::any_cast<std::pair<crane::obj, crane::obj>>(
                      std::move(_result))
                      .first;
      } else if (std::holds_alternative<CraneCont_Ite>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Ite>(_frame));
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        if (crane::any_cast<bool>(std::move(_result))) {
          _stack.emplace_back(CraneEnter{&a1});
        } else {
          _stack.emplace_back(CraneEnter{&a2});
        }
      } else if (std::holds_alternative<CraneCont_PairE>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE>(_frame));
        const expr &b = *_f.b;
        _stack.emplace_back(CraneCont_PairE_1{std::move(_result)});
        _stack.emplace_back(CraneEnter{&b});
      } else if (std::holds_alternative<CraneCont_PairE_1>(_frame)) {
        auto _f = std::move(std::get<CraneCont_PairE_1>(_frame));
        _result = std::make_pair(crane::obj(_f._tmp4),
                                 crane::obj(std::move(_result)));
      } else {
        auto _f = std::move(std::get<CraneCont_SuccE>(_frame));
        _result = (crane::any_cast<uint64_t>(std::move(_result)) + 1);
      }
    }
    return _result;
  }

  static inline const expr sample = expr::fste(
      expr::paire(expr::succe(expr::lit(UINT64_C(3))), expr::bl(true)));

  static inline const uint64_t run =
      crane::any_cast<uint64_t>(eval<uint64_t>(sample));
};

#endif // INCLUDED_LOOPIFY_EXISTENTIAL_RECURSIVE_CALL
