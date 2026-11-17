#ifndef INCLUDED_RECURSOR_METHOD_HEAD_SIBLING
#define INCLUDED_RECURSOR_METHOD_HEAD_SIBLING

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A type-indexed family's recursor, made a method, next to an unrelated
/// inductive.
///
/// With chain declared beside expr, expr_rect becomes a method of
/// expr (alone, it stays a function), and the method's head drops the
/// index variable T2.  The check that the body names no variable the
/// head dropped reported that it names T2, though the printed C++ names
/// it nowhere: the method's own self-call carries every type argument,
/// and is printed on its receiver without the ones the head dropped.  The
/// check now reads a method callee's type arguments as they are printed.
struct RecursorMethodHeadSibling {
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

    using variant_t = std::variant<Lit, Bl, SuccE>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    expr() {}

    explicit expr(Lit _v) : v_(std::move(_v)) {}

    explicit expr(Bl _v) : v_(std::move(_v)) {}

    explicit expr(SuccE _v) : v_(std::move(_v)) {}

    static expr lit(uint64_t a0) { return expr(Lit{a0}); }

    static expr bl(bool a0) { return expr(Bl{a0}); }

    static expr succe(expr a0) {
      return expr(SuccE{std::make_shared<expr>(std::move(a0))});
    }

    // MANIPULATORS
    ~expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<expr> {
        if (auto *_alt = std::get_if<SuccE>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<expr> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    expr(const expr &) = default;
    expr &operator=(const expr &) = default;
    expr(expr &&) = default;
    expr &operator=(expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, const bool &>
    T1 expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of expr_rec: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_expr_rec_in_SuccE {
        std::shared_ptr<expr> a0;
      };

      using _frame = std::variant<_call, _after_expr_rec_in_SuccE>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame _popped = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Bl>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Bl>(_sv.v());
            _result = f0(a0);
          } else {
            const auto &[a0] = std::get<typename expr::SuccE>(_sv.v());
            _stack.emplace_back(_after_expr_rec_in_SuccE{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_after_expr_rec_in_SuccE>(_popped));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          _result = f1(*a0, std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, const bool &>
    T1 expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const expr *_self = this;

      // Explicit stack replaces the non-tail recursion of expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const expr *_self;
      };

      struct _after_expr_rect_in_SuccE {
        std::shared_ptr<expr> a0;
      };

      using _frame = std::variant<_call, _after_expr_rect_in_SuccE>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame _popped = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          const expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename expr::Lit>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Lit>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename expr::Bl>(_sv.v())) {
            const auto &[a0] = std::get<typename expr::Bl>(_sv.v());
            _result = f0(a0);
          } else {
            const auto &[a0] = std::get<typename expr::SuccE>(_sv.v());
            _stack.emplace_back(_after_expr_rect_in_SuccE{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_after_expr_rect_in_SuccE>(_popped));
          std::shared_ptr<expr> a0 = std::move(_f.a0);
          _result = f1(*a0, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct chain {
    // TYPES
    struct Base {
      uint64_t a0;
    };

    struct Next {
      std::shared_ptr<chain> a0;
    };

    using variant_t = std::variant<Base, Next>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Base _v) : v_(std::move(_v)) {}

    explicit chain(Next _v) : v_(std::move(_v)) {}

    static chain base(uint64_t a0) { return chain(Base{a0}); }

    static chain next(chain a0) {
      return chain(Next{std::make_shared<chain>(std::move(a0))});
    }

    // MANIPULATORS
    ~chain() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<chain> {
        if (auto *_alt = std::get_if<Next>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<chain> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) = default;
    chain &operator=(chain &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
    T1 chain_rec(F0 &&f, F1 &&f0) const {
      return this->template chain_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 chain_rect(F0 &&f, F1 &&f0) const {
      const chain *_self = this;

      // Explicit stack replaces the non-tail recursion of chain_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const chain *_self;
      };

      struct _after_chain_rect_in_Next {
        std::shared_ptr<chain> a0;
      };

      using _frame = std::variant<_call, _after_chain_rect_in_Next>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame _popped = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          const chain *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename chain::Base>(_sv.v())) {
            const auto &[a0] = std::get<typename chain::Base>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0] = std::get<typename chain::Next>(_sv.v());
            _stack.emplace_back(_after_chain_rect_in_Next{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else {
          auto _f = std::move(std::get<_after_chain_rect_in_Next>(_popped));
          std::shared_ptr<chain> a0 = std::move(_f.a0);
          _result = f0(*a0, std::move(_result));
        }
      }
      return _result;
    }
  };

  static inline const expr sample = expr::succe(expr::lit(UINT64_C(1)));
  static inline const chain sample_chain =
      chain::next(chain::base(UINT64_C(1)));
};

#endif // INCLUDED_RECURSOR_METHOD_HEAD_SIBLING
