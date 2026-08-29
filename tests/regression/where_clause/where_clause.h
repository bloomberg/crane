#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct WhereClause {
  struct Expr {
    // TYPES
    struct Num {
      uint64_t a0;
    };

    struct Plus {
      std::shared_ptr<Expr> a0;
      std::shared_ptr<Expr> a1;
    };

    struct Times {
      std::shared_ptr<Expr> a0;
      std::shared_ptr<Expr> a1;
    };

    using variant_t = std::variant<Num, Plus, Times>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Expr() {}

    explicit Expr(Num _v) : v_(std::move(_v)) {}

    explicit Expr(Plus _v) : v_(std::move(_v)) {}

    explicit Expr(Times _v) : v_(std::move(_v)) {}

    static Expr num(uint64_t a0) { return Expr(Num{a0}); }

    static Expr plus(Expr a0, Expr a1) {
      return Expr(Plus{std::make_shared<Expr>(std::move(a0)),
                       std::make_shared<Expr>(std::move(a1))});
    }

    static Expr times(Expr a0, Expr a1) {
      return Expr(Times{std::make_shared<Expr>(std::move(a0)),
                        std::make_shared<Expr>(std::move(a1))});
    }

    // MANIPULATORS
    ~Expr() {
      crane::small_vector<std::shared_ptr<Expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Plus>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<Times>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    Expr(const Expr &) = default;
    Expr &operator=(const Expr &) = default;
    Expr(Expr &&) noexcept = default;
    Expr &operator=(Expr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t expr_size() const {
      const Expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const Expr *_self;
      };

      /// _After_Plus: saves [a0, _s1], dispatches next recursive call.
      struct _After_Plus {
        Expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _After_Times: saves [a0, _s1], dispatches next recursive call.
      struct _After_Times {
        Expr *a0;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Combine_Plus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Plus {
        uint64_t _result;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      /// _Combine_Times: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Times {
        uint64_t _result;
        std::decay_t<decltype(UINT64_C(1))> _s1;
      };

      using _Frame = std::variant<_Enter, _After_Plus, _After_Times,
                                  _Combine_Plus, _Combine_Times>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified expr_size: _Enter -> _After_Plus -> _After_Times ->
      /// _Combine_Plus -> _Combine_Times.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(_After_Plus{crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(_After_Times{crane_raw(a0), UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Plus>(_frame)) {
          auto _f = std::move(std::get<_After_Plus>(_frame));
          _stack.emplace_back(_Combine_Plus{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_Times>(_frame)) {
          auto _f = std::move(std::get<_After_Times>(_frame));
          _stack.emplace_back(_Combine_Times{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_Plus>(_frame)) {
          auto _f = std::move(std::get<_Combine_Plus>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Times>(_frame));
          _result = ((_f._s1 + std::move(_result)) + std::move(_f._result));
        }
      }
      return _result;
    }

    uint64_t eval() const {
      const Expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const Expr *_self;
      };

      /// _After_Plus: saves [a0], dispatches next recursive call.
      struct _After_Plus {
        Expr *a0;
      };

      /// _After_Times: saves [a0], dispatches next recursive call.
      struct _After_Times {
        Expr *a0;
      };

      /// _Combine_Plus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Plus {
        uint64_t _result;
      };

      /// _Combine_Times: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Times {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_Plus, _After_Times,
                                  _Combine_Plus, _Combine_Times>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified eval: _Enter -> _After_Plus -> _After_Times -> _Combine_Plus
      /// -> _Combine_Times.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            const auto &[a0] = std::get<typename Expr::Num>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(_After_Plus{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(_After_Times{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Plus>(_frame)) {
          auto _f = std::move(std::get<_After_Plus>(_frame));
          _stack.emplace_back(_Combine_Plus{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_Times>(_frame)) {
          auto _f = std::move(std::get<_After_Times>(_frame));
          _stack.emplace_back(_Combine_Times{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_Plus>(_frame)) {
          auto _f = std::move(std::get<_Combine_Plus>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Times>(_frame));
          _result = (std::move(_result) * std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, Expr &, T1 &, Expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, Expr &, T1 &, Expr &, T1 &>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const Expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const Expr *_self;
      };

      /// _After_Plus: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Plus {
        Expr *a0_0;
        Expr a1;
        Expr a0_1;
      };

      /// _After_Times: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Times {
        Expr *a0_0;
        Expr a1;
        Expr a0_1;
      };

      /// _Combine_Plus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Plus {
        std::decay_t<T1> _result;
        Expr a1;
        Expr a0;
      };

      /// _Combine_Times: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Times {
        std::decay_t<T1> _result;
        Expr a1;
        Expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Plus, _After_Times,
                                  _Combine_Plus, _Combine_Times>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified Expr_rec: _Enter -> _After_Plus -> _After_Times ->
      /// _Combine_Plus -> _Combine_Times.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            const auto &[a0] = std::get<typename Expr::Num>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(_After_Plus{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(_After_Times{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Plus>(_frame)) {
          auto _f = std::move(std::get<_After_Plus>(_frame));
          _stack.emplace_back(_Combine_Plus{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_Times>(_frame)) {
          auto _f = std::move(std::get<_After_Times>(_frame));
          _stack.emplace_back(_Combine_Times{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_Plus>(_frame)) {
          auto _f = std::move(std::get<_Combine_Plus>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Times>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, Expr &, T1 &, Expr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, Expr &, T1 &, Expr &, T1 &>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const Expr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const Expr *_self;
      };

      /// _After_Plus: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Plus {
        Expr *a0_0;
        Expr a1;
        Expr a0_1;
      };

      /// _After_Times: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_Times {
        Expr *a0_0;
        Expr a1;
        Expr a0_1;
      };

      /// _Combine_Plus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Plus {
        std::decay_t<T1> _result;
        Expr a1;
        Expr a0;
      };

      /// _Combine_Times: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Times {
        std::decay_t<T1> _result;
        Expr a1;
        Expr a0;
      };

      using _Frame = std::variant<_Enter, _After_Plus, _After_Times,
                                  _Combine_Plus, _Combine_Times>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified Expr_rect: _Enter -> _After_Plus -> _After_Times ->
      /// _Combine_Plus -> _Combine_Times.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            const auto &[a0] = std::get<typename Expr::Num>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(_After_Plus{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(_After_Times{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_Plus>(_frame)) {
          auto _f = std::move(std::get<_After_Plus>(_frame));
          _stack.emplace_back(_Combine_Plus{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_Times>(_frame)) {
          auto _f = std::move(std::get<_After_Times>(_frame));
          _stack.emplace_back(_Combine_Times{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_Plus>(_frame)) {
          auto _f = std::move(std::get<_Combine_Plus>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_Times>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };

  struct BExpr {
    // TYPES
    struct BTrue {};

    struct BFalse {};

    struct BAnd {
      std::shared_ptr<BExpr> a0;
      std::shared_ptr<BExpr> a1;
    };

    struct BOr {
      std::shared_ptr<BExpr> a0;
      std::shared_ptr<BExpr> a1;
    };

    struct BNot {
      std::shared_ptr<BExpr> a0;
    };

    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    BExpr() {}

    explicit BExpr(BTrue _v) : v_(_v) {}

    explicit BExpr(BFalse _v) : v_(_v) {}

    explicit BExpr(BAnd _v) : v_(std::move(_v)) {}

    explicit BExpr(BOr _v) : v_(std::move(_v)) {}

    explicit BExpr(BNot _v) : v_(std::move(_v)) {}

    static BExpr btrue() { return BExpr(BTrue{}); }

    static BExpr bfalse() { return BExpr(BFalse{}); }

    static BExpr band(BExpr a0, BExpr a1) {
      return BExpr(BAnd{std::make_shared<BExpr>(std::move(a0)),
                        std::make_shared<BExpr>(std::move(a1))});
    }

    static BExpr bor(BExpr a0, BExpr a1) {
      return BExpr(BOr{std::make_shared<BExpr>(std::move(a0)),
                       std::make_shared<BExpr>(std::move(a1))});
    }

    static BExpr bnot(BExpr a0) {
      return BExpr(BNot{std::make_shared<BExpr>(std::move(a0))});
    }

    // MANIPULATORS
    ~BExpr() {
      crane::small_vector<std::shared_ptr<BExpr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BAnd>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BOr>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BNot>(&_v)) {
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

    BExpr(const BExpr &) = default;
    BExpr &operator=(const BExpr &) = default;
    BExpr(BExpr &&) noexcept = default;
    BExpr &operator=(BExpr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool beval() const {
      const BExpr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const BExpr *_self;
      };

      /// _After_BAnd: saves [a0], dispatches next recursive call.
      struct _After_BAnd {
        BExpr *a0;
      };

      /// _After_BOr: saves [a0], dispatches next recursive call.
      struct _After_BOr {
        BExpr *a0;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        bool _result;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        bool _result;
      };

      /// _Resume_BNot: resumes after recursive call with _result.
      struct _Resume_BNot {};

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      bool _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified beval: _Enter -> _After_BAnd -> _After_BOr -> _Combine_BAnd
      /// -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const BExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
            _result = true;
          } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
            _result = false;
          } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0] = std::get<typename BExpr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(_Combine_BAnd{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(_Combine_BOr{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = (std::move(_result) && std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = (std::move(_result) || std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = !(std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, BExpr &, T1 &>
    T1 BExpr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const BExpr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const BExpr *_self;
      };

      /// _After_BAnd: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BAnd {
        BExpr *a0_0;
        BExpr a1;
        BExpr a0_1;
      };

      /// _After_BOr: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BOr {
        BExpr *a0_0;
        BExpr a1;
        BExpr a0_1;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        std::decay_t<T1> _result;
        BExpr a1;
        BExpr a0;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        std::decay_t<T1> _result;
        BExpr a1;
        BExpr a0;
      };

      /// _Resume_BNot: saves [a0], resumes after recursive call with _result.
      struct _Resume_BNot {
        BExpr a0;
      };

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified BExpr_rec: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const BExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0] = std::get<typename BExpr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{*a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(_Combine_BAnd{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(_Combine_BOr{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = f2(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = f3(std::move(_f.a0), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
      requires std::is_invocable_r_v<T1, F2 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F3 &, BExpr &, T1 &, BExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F4 &, BExpr &, T1 &>
    T1 BExpr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const BExpr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const BExpr *_self;
      };

      /// _After_BAnd: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BAnd {
        BExpr *a0_0;
        BExpr a1;
        BExpr a0_1;
      };

      /// _After_BOr: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BOr {
        BExpr *a0_0;
        BExpr a1;
        BExpr a0_1;
      };

      /// _Combine_BAnd: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BAnd {
        std::decay_t<T1> _result;
        BExpr a1;
        BExpr a0;
      };

      /// _Combine_BOr: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BOr {
        std::decay_t<T1> _result;
        BExpr a1;
        BExpr a0;
      };

      /// _Resume_BNot: saves [a0], resumes after recursive call with _result.
      struct _Resume_BNot {
        BExpr a0;
      };

      using _Frame = std::variant<_Enter, _After_BAnd, _After_BOr,
                                  _Combine_BAnd, _Combine_BOr, _Resume_BNot>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified BExpr_rect: _Enter -> _After_BAnd -> _After_BOr ->
      /// _Combine_BAnd -> _Combine_BOr -> _Resume_BNot.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const BExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BAnd>(_sv.v());
            _stack.emplace_back(_After_BAnd{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BOr>(_sv.v());
            _stack.emplace_back(_After_BOr{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0] = std::get<typename BExpr::BNot>(_sv.v());
            _stack.emplace_back(_Resume_BNot{*a0});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_BAnd>(_frame)) {
          auto _f = std::move(std::get<_After_BAnd>(_frame));
          _stack.emplace_back(_Combine_BAnd{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_After_BOr>(_frame)) {
          auto _f = std::move(std::get<_After_BOr>(_frame));
          _stack.emplace_back(_Combine_BOr{std::move(_result), std::move(_f.a1),
                                           std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else if (std::holds_alternative<_Combine_BAnd>(_frame)) {
          auto _f = std::move(std::get<_Combine_BAnd>(_frame));
          _result = f1(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else if (std::holds_alternative<_Combine_BOr>(_frame)) {
          auto _f = std::move(std::get<_Combine_BOr>(_frame));
          _result = f2(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Resume_BNot>(_frame));
          _result = f3(std::move(_f.a0), std::move(_result));
        }
      }
      return _result;
    }
  };

  struct AExpr {
    // TYPES
    struct ANum {
      uint64_t a0;
    };

    struct APlus {
      std::shared_ptr<AExpr> a0;
      std::shared_ptr<AExpr> a1;
    };

    struct AIf {
      BExpr a0;
      std::shared_ptr<AExpr> a1;
      std::shared_ptr<AExpr> a2;
    };

    using variant_t = std::variant<ANum, APlus, AIf>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    AExpr() {}

    explicit AExpr(ANum _v) : v_(std::move(_v)) {}

    explicit AExpr(APlus _v) : v_(std::move(_v)) {}

    explicit AExpr(AIf _v) : v_(std::move(_v)) {}

    static AExpr anum(uint64_t a0) { return AExpr(ANum{a0}); }

    static AExpr aplus(AExpr a0, AExpr a1) {
      return AExpr(APlus{std::make_shared<AExpr>(std::move(a0)),
                         std::make_shared<AExpr>(std::move(a1))});
    }

    static AExpr aif(BExpr a0, AExpr a1, AExpr a2) {
      return AExpr(AIf{std::move(a0), std::make_shared<AExpr>(std::move(a1)),
                       std::make_shared<AExpr>(std::move(a2))});
    }

    // MANIPULATORS
    ~AExpr() {
      crane::small_vector<std::shared_ptr<AExpr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<APlus>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<AIf>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
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

    AExpr(const AExpr &) = default;
    AExpr &operator=(const AExpr &) = default;
    AExpr(AExpr &&) noexcept = default;
    AExpr &operator=(AExpr &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t aeval() const {
      const AExpr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const AExpr *_self;
      };

      /// _After_APlus: saves [a0], dispatches next recursive call.
      struct _After_APlus {
        AExpr *a0;
      };

      /// _Combine_APlus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_APlus {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_APlus, _Combine_APlus>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified aeval: _Enter -> _After_APlus -> _Combine_APlus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const AExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename AExpr::ANum>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename AExpr::APlus>(_sv.v());
            _stack.emplace_back(_After_APlus{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename AExpr::AIf>(_sv.v());
            if (a0.beval()) {
              _stack.emplace_back(_Enter{crane_raw(a1)});
            } else {
              _stack.emplace_back(_Enter{crane_raw(a2)});
            }
          }
        } else if (std::holds_alternative<_After_APlus>(_frame)) {
          auto _f = std::move(std::get<_After_APlus>(_frame));
          _stack.emplace_back(_Combine_APlus{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_APlus>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, AExpr &, T1 &, AExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, BExpr &, AExpr &, T1 &, AExpr &,
                                     T1 &>
    T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      const AExpr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const AExpr *_self;
      };

      /// _After_AIf: saves [a3_0, a4, a3_1, a2], dispatches next recursive
      /// call.
      struct _After_AIf {
        AExpr *a3_0;
        AExpr a4;
        AExpr a3_1;
        BExpr a2;
      };

      /// _After_APlus: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_APlus {
        AExpr *a2_0;
        AExpr a3;
        AExpr a2_1;
      };

      /// _Combine_AIf: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AIf {
        std::decay_t<T1> _result;
        AExpr a4;
        AExpr a3;
        BExpr a2;
      };

      /// _Combine_APlus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_APlus {
        std::decay_t<T1> _result;
        AExpr a3;
        AExpr a2;
      };

      using _Frame = std::variant<_Enter, _After_AIf, _After_APlus,
                                  _Combine_AIf, _Combine_APlus>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified AExpr_rec: _Enter -> _After_AIf -> _After_APlus ->
      /// _Combine_AIf -> _Combine_APlus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const AExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename AExpr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
            const auto &[a2, a3] = std::get<typename AExpr::APlus>(_sv.v());
            _stack.emplace_back(_After_APlus{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          } else {
            const auto &[a2, a3, a4] = std::get<typename AExpr::AIf>(_sv.v());
            _stack.emplace_back(_After_AIf{crane_raw(a3), *a4, *a3, a2});
            _stack.emplace_back(_Enter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<_After_AIf>(_frame)) {
          auto _f = std::move(std::get<_After_AIf>(_frame));
          _stack.emplace_back(_Combine_AIf{std::move(_result), std::move(_f.a4),
                                           std::move(_f.a3_1),
                                           std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f.a3_0});
        } else if (std::holds_alternative<_After_APlus>(_frame)) {
          auto _f = std::move(std::get<_After_APlus>(_frame));
          _stack.emplace_back(_Combine_APlus{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_Combine_AIf>(_frame)) {
          auto _f = std::move(std::get<_Combine_AIf>(_frame));
          _result = f1(std::move(_f.a2), std::move(_f.a3), std::move(_result),
                       std::move(_f.a4), std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_APlus>(_frame));
          _result = f0(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, AExpr &, T1 &, AExpr &, T1 &> &&
               std::is_invocable_r_v<T1, F2 &, BExpr &, AExpr &, T1 &, AExpr &,
                                     T1 &>
    T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const AExpr *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const AExpr *_self;
      };

      /// _After_AIf: saves [a3_0, a4, a3_1, a2], dispatches next recursive
      /// call.
      struct _After_AIf {
        AExpr *a3_0;
        AExpr a4;
        AExpr a3_1;
        BExpr a2;
      };

      /// _After_APlus: saves [a2_0, a3, a2_1], dispatches next recursive call.
      struct _After_APlus {
        AExpr *a2_0;
        AExpr a3;
        AExpr a2_1;
      };

      /// _Combine_AIf: receives partial results, combines with _result from
      /// final call.
      struct _Combine_AIf {
        std::decay_t<T1> _result;
        AExpr a4;
        AExpr a3;
        BExpr a2;
      };

      /// _Combine_APlus: receives partial results, combines with _result from
      /// final call.
      struct _Combine_APlus {
        std::decay_t<T1> _result;
        AExpr a3;
        AExpr a2;
      };

      using _Frame = std::variant<_Enter, _After_AIf, _After_APlus,
                                  _Combine_AIf, _Combine_APlus>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified AExpr_rect: _Enter -> _After_AIf -> _After_APlus ->
      /// _Combine_AIf -> _Combine_APlus.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const AExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename AExpr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
            const auto &[a2, a3] = std::get<typename AExpr::APlus>(_sv.v());
            _stack.emplace_back(_After_APlus{crane_raw(a2), *a3, *a2});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          } else {
            const auto &[a2, a3, a4] = std::get<typename AExpr::AIf>(_sv.v());
            _stack.emplace_back(_After_AIf{crane_raw(a3), *a4, *a3, a2});
            _stack.emplace_back(_Enter{crane_raw(a4)});
          }
        } else if (std::holds_alternative<_After_AIf>(_frame)) {
          auto _f = std::move(std::get<_After_AIf>(_frame));
          _stack.emplace_back(_Combine_AIf{std::move(_result), std::move(_f.a4),
                                           std::move(_f.a3_1),
                                           std::move(_f.a2)});
          _stack.emplace_back(_Enter{_f.a3_0});
        } else if (std::holds_alternative<_After_APlus>(_frame)) {
          auto _f = std::move(std::get<_After_APlus>(_frame));
          _stack.emplace_back(_Combine_APlus{
              std::move(_result), std::move(_f.a3), std::move(_f.a2_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_Combine_AIf>(_frame)) {
          auto _f = std::move(std::get<_Combine_AIf>(_frame));
          _result = f1(std::move(_f.a2), std::move(_f.a3), std::move(_result),
                       std::move(_f.a4), std::move(_f._result));
        } else {
          auto _f = std::move(std::get<_Combine_APlus>(_frame));
          _result = f0(std::move(_f.a2), std::move(_result), std::move(_f.a3),
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };

  static inline const uint64_t test_eval_plus =
      Expr::plus(Expr::num(UINT64_C(3)), Expr::num(UINT64_C(4))).eval();
  static inline const uint64_t test_eval_times =
      Expr::times(Expr::num(UINT64_C(5)), Expr::num(UINT64_C(6))).eval();
  static inline const uint64_t test_eval_nested =
      Expr::plus(Expr::times(Expr::num(UINT64_C(2)), Expr::num(UINT64_C(3))),
                 Expr::num(UINT64_C(1)))
          .eval();
  static inline const uint64_t test_size =
      Expr::plus(Expr::times(Expr::num(UINT64_C(2)), Expr::num(UINT64_C(3))),
                 Expr::num(UINT64_C(1)))
          .expr_size();
  static inline const bool test_beval =
      BExpr::band(BExpr::btrue(), BExpr::bnot(BExpr::bfalse())).beval();
  static inline const uint64_t test_aeval =
      AExpr::aif(BExpr::band(BExpr::btrue(), BExpr::btrue()),
                 AExpr::anum(UINT64_C(10)), AExpr::anum(UINT64_C(20)))
          .aeval();
};

#endif // INCLUDED_WHERE_CLAUSE
