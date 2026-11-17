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

    static expr succe(crane::shared_child_slot<expr> a0) {
      return expr(SuccE{a0.take()});
    }

    static expr ite(crane::shared_child_slot<expr> a,
                    crane::shared_child_slot<expr> a1,
                    crane::shared_child_slot<expr> a2) {
      return expr(Ite{a.take(), a1.take(), a2.take()});
    }

    static expr paire(crane::shared_child_slot<expr> a,
                      crane::shared_child_slot<expr> b) {
      return expr(PairE{a.take(), b.take()});
    }

    static expr fste(crane::shared_child_slot<expr> a) {
      return expr(FstE{a.take()});
    }

    // MANIPULATORS
    ~expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
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
    // Explicit stack replaces the non-tail recursion of expr_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const expr *e;
    };

    struct _after_expr_rect_in_FstE {
      std::shared_ptr<expr> a;
    };

    struct _after_expr_rect_in_Ite {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
    };

    struct _after_expr_rect_in_Ite_2 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
    };

    struct _after_expr_rect_in_Ite_3 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
      T1 _tmp3;
    };

    struct _after_expr_rect_in_PairE {
      std::shared_ptr<expr> a;
      const expr *b;
    };

    struct _after_expr_rect_in_PairE_2 {
      std::shared_ptr<expr> a;
      const expr *b;
      T1 _tmp6;
    };

    struct _after_expr_rect_in_SuccE {
      std::shared_ptr<expr> a0;
    };

    using _frame =
        std::variant<_call, _after_expr_rect_in_FstE, _after_expr_rect_in_Ite,
                     _after_expr_rect_in_Ite_2, _after_expr_rect_in_Ite_3,
                     _after_expr_rect_in_PairE, _after_expr_rect_in_PairE_2,
                     _after_expr_rect_in_SuccE>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&e});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const expr &e = *_f.e;
        if (std::holds_alternative<typename expr::Lit>(e.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(e.v());
          _result = f(a0);
        } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
          const auto &[a0] = std::get<typename expr::Bl>(e.v());
          _result = f0(a0);
        } else if (std::holds_alternative<typename expr::SuccE>(e.v())) {
          const auto &[a0] = std::get<typename expr::SuccE>(e.v());
          _stack.emplace_back(_after_expr_rect_in_SuccE{a0});
          _stack.emplace_back(_call{crane_raw(a0)});
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(
              _after_expr_rect_in_Ite{a, crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _stack.emplace_back(_after_expr_rect_in_PairE{a, crane_raw(b)});
          _stack.emplace_back(_call{crane_raw(a)});
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _stack.emplace_back(_after_expr_rect_in_FstE{a});
          _stack.emplace_back(_call{crane_raw(a)});
        }
      } else if (std::holds_alternative<_after_expr_rect_in_FstE>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rect_in_FstE>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        _result = crane_any_cast<T1>(f4(*a, std::move(_result)));
      } else if (std::holds_alternative<_after_expr_rect_in_Ite>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rect_in_Ite>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(_after_expr_rect_in_Ite_2{std::move(a), &a1, &a2,
                                                      std::move(_result)});
        _stack.emplace_back(_call{&a1});
      } else if (std::holds_alternative<_after_expr_rect_in_Ite_2>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rect_in_Ite_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(_after_expr_rect_in_Ite_3{
            std::move(a), &a1, &a2, std::move(_f._tmp4), std::move(_result)});
        _stack.emplace_back(_call{&a2});
      } else if (std::holds_alternative<_after_expr_rect_in_Ite_3>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rect_in_Ite_3>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f2(*a, std::move(_f._tmp4), a1,
                                  std::move(_f._tmp3), a2, std::move(_result)));
      } else if (std::holds_alternative<_after_expr_rect_in_PairE>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rect_in_PairE>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _stack.emplace_back(
            _after_expr_rect_in_PairE_2{std::move(a), &b, std::move(_result)});
        _stack.emplace_back(_call{&b});
      } else if (std::holds_alternative<_after_expr_rect_in_PairE_2>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rect_in_PairE_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _result = crane_any_cast<T1>(
            f3(*a, std::move(_f._tmp6), b, std::move(_result)));
      } else {
        auto _f = std::move(std::get<_after_expr_rect_in_SuccE>(_popped));
        _stack.pop_back();
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
                     const expr &e) {
    // Explicit stack replaces the non-tail recursion of expr_rec: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const expr *e;
    };

    struct _after_expr_rec_in_FstE {
      std::shared_ptr<expr> a;
    };

    struct _after_expr_rec_in_Ite {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
    };

    struct _after_expr_rec_in_Ite_2 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
    };

    struct _after_expr_rec_in_Ite_3 {
      std::shared_ptr<expr> a;
      const expr *a1;
      const expr *a2;
      T1 _tmp4;
      T1 _tmp3;
    };

    struct _after_expr_rec_in_PairE {
      std::shared_ptr<expr> a;
      const expr *b;
    };

    struct _after_expr_rec_in_PairE_2 {
      std::shared_ptr<expr> a;
      const expr *b;
      T1 _tmp6;
    };

    struct _after_expr_rec_in_SuccE {
      std::shared_ptr<expr> a0;
    };

    using _frame =
        std::variant<_call, _after_expr_rec_in_FstE, _after_expr_rec_in_Ite,
                     _after_expr_rec_in_Ite_2, _after_expr_rec_in_Ite_3,
                     _after_expr_rec_in_PairE, _after_expr_rec_in_PairE_2,
                     _after_expr_rec_in_SuccE>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&e});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const expr &e = *_f.e;
        if (std::holds_alternative<typename expr::Lit>(e.v())) {
          const auto &[a0] = std::get<typename expr::Lit>(e.v());
          _result = f(a0);
        } else if (std::holds_alternative<typename expr::Bl>(e.v())) {
          const auto &[a0] = std::get<typename expr::Bl>(e.v());
          _result = f0(a0);
        } else if (std::holds_alternative<typename expr::SuccE>(e.v())) {
          const auto &[a0] = std::get<typename expr::SuccE>(e.v());
          _stack.emplace_back(_after_expr_rec_in_SuccE{a0});
          _stack.emplace_back(_call{crane_raw(a0)});
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(
              _after_expr_rec_in_Ite{a, crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _stack.emplace_back(_after_expr_rec_in_PairE{a, crane_raw(b)});
          _stack.emplace_back(_call{crane_raw(a)});
        } else {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _stack.emplace_back(_after_expr_rec_in_FstE{a});
          _stack.emplace_back(_call{crane_raw(a)});
        }
      } else if (std::holds_alternative<_after_expr_rec_in_FstE>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rec_in_FstE>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        _result = crane_any_cast<T1>(f4(*a, std::move(_result)));
      } else if (std::holds_alternative<_after_expr_rec_in_Ite>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rec_in_Ite>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(_after_expr_rec_in_Ite_2{std::move(a), &a1, &a2,
                                                     std::move(_result)});
        _stack.emplace_back(_call{&a1});
      } else if (std::holds_alternative<_after_expr_rec_in_Ite_2>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rec_in_Ite_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(_after_expr_rec_in_Ite_3{
            std::move(a), &a1, &a2, std::move(_f._tmp4), std::move(_result)});
        _stack.emplace_back(_call{&a2});
      } else if (std::holds_alternative<_after_expr_rec_in_Ite_3>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rec_in_Ite_3>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _result =
            crane_any_cast<T1>(f2(*a, std::move(_f._tmp4), a1,
                                  std::move(_f._tmp3), a2, std::move(_result)));
      } else if (std::holds_alternative<_after_expr_rec_in_PairE>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rec_in_PairE>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _stack.emplace_back(
            _after_expr_rec_in_PairE_2{std::move(a), &b, std::move(_result)});
        _stack.emplace_back(_call{&b});
      } else if (std::holds_alternative<_after_expr_rec_in_PairE_2>(_popped)) {
        auto _f = std::move(std::get<_after_expr_rec_in_PairE_2>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a = std::move(_f.a);
        const expr &b = *_f.b;
        _result = crane_any_cast<T1>(
            f3(*a, std::move(_f._tmp6), b, std::move(_result)));
      } else {
        auto _f = std::move(std::get<_after_expr_rec_in_SuccE>(_popped));
        _stack.pop_back();
        std::shared_ptr<expr> a0 = std::move(_f.a0);
        _result = f1(*a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1 = void> static uint64_t size(const expr &e) {
    // Explicit stack replaces the non-tail recursion of size: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const expr *e;
    };

    struct _after_size_in_FstE {};

    struct _after_size_in_Ite {
      const expr *a1;
      const expr *a2;
    };

    struct _after_size_in_Ite_2 {
      const expr *a2;
      uint64_t _tmp4;
    };

    struct _after_size_in_Ite_3 {
      uint64_t _tmp4;
      uint64_t _tmp3;
    };

    struct _after_size_in_PairE {
      const expr *b;
    };

    struct _after_size_in_PairE_2 {
      uint64_t _tmp6;
    };

    struct _after_size_in_SuccE {};

    using _frame = std::variant<_call, _after_size_in_FstE, _after_size_in_Ite,
                                _after_size_in_Ite_2, _after_size_in_Ite_3,
                                _after_size_in_PairE, _after_size_in_PairE_2,
                                _after_size_in_SuccE>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&e});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const expr &e = *_f.e;
        if (std::holds_alternative<typename expr::SuccE>(e.v())) {
          const auto &[a0] = std::get<typename expr::SuccE>(e.v());
          _stack.emplace_back(_after_size_in_SuccE{});
          _stack.emplace_back(_call{crane_raw(a0)});
        } else if (std::holds_alternative<typename expr::Ite>(e.v())) {
          const auto &[a, a1, a2] = std::get<typename expr::Ite>(e.v());
          _stack.emplace_back(_after_size_in_Ite{crane_raw(a1), crane_raw(a2)});
          _stack.emplace_back(_call{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::PairE>(e.v())) {
          const auto &[a, b] = std::get<typename expr::PairE>(e.v());
          _stack.emplace_back(_after_size_in_PairE{crane_raw(b)});
          _stack.emplace_back(_call{crane_raw(a)});
        } else if (std::holds_alternative<typename expr::FstE>(e.v())) {
          const auto &[a] = std::get<typename expr::FstE>(e.v());
          _stack.emplace_back(_after_size_in_FstE{});
          _stack.emplace_back(_call{crane_raw(a)});
        } else {
          _result = UINT64_C(1);
        }
      } else if (std::holds_alternative<_after_size_in_FstE>(_popped)) {
        auto _f = std::move(std::get<_after_size_in_FstE>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      } else if (std::holds_alternative<_after_size_in_Ite>(_popped)) {
        auto _f = std::move(std::get<_after_size_in_Ite>(_popped));
        _stack.pop_back();
        const expr &a1 = *_f.a1;
        const expr &a2 = *_f.a2;
        _stack.emplace_back(_after_size_in_Ite_2{&a2, std::move(_result)});
        _stack.emplace_back(_call{&a1});
      } else if (std::holds_alternative<_after_size_in_Ite_2>(_popped)) {
        auto _f = std::move(std::get<_after_size_in_Ite_2>(_popped));
        _stack.pop_back();
        const expr &a2 = *_f.a2;
        _stack.emplace_back(_after_size_in_Ite_3{_f._tmp4, std::move(_result)});
        _stack.emplace_back(_call{&a2});
      } else if (std::holds_alternative<_after_size_in_Ite_3>(_popped)) {
        auto _f = std::move(std::get<_after_size_in_Ite_3>(_popped));
        _stack.pop_back();
        _result = (((_f._tmp4 + _f._tmp3) + std::move(_result)) + 1);
      } else if (std::holds_alternative<_after_size_in_PairE>(_popped)) {
        auto _f = std::move(std::get<_after_size_in_PairE>(_popped));
        _stack.pop_back();
        const expr &b = *_f.b;
        _stack.emplace_back(_after_size_in_PairE_2{std::move(_result)});
        _stack.emplace_back(_call{&b});
      } else if (std::holds_alternative<_after_size_in_PairE_2>(_popped)) {
        auto _f = std::move(std::get<_after_size_in_PairE_2>(_popped));
        _stack.pop_back();
        _result = ((_f._tmp6 + std::move(_result)) + 1);
      } else {
        auto _f = std::move(std::get<_after_size_in_SuccE>(_popped));
        _stack.pop_back();
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
