#ifndef INCLUDED_WHERE_CLAUSE
#define INCLUDED_WHERE_CLAUSE

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
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

    static Expr plus(crane::shared_child_slot<Expr> a0,
                     crane::shared_child_slot<Expr> a1) {
      return Expr(Plus{a0.take(), a1.take()});
    }

    static Expr times(crane::shared_child_slot<Expr> a0,
                      crane::shared_child_slot<Expr> a1) {
      return Expr(Times{a0.take(), a1.take()});
    }

    // MANIPULATORS
    ~Expr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Num>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Plus>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<Times>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<Expr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Plus>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<Times>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
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
    Expr(Expr &&) = default;
    Expr &operator=(Expr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t expr_size() const {
      const Expr *_self = this;

      // Explicit stack replaces the non-tail recursion of expr_size: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const Expr *_self;
      };

      struct _after_expr_size_in_Plus {
        const Expr *a1;
      };

      struct _after_expr_size_in_Plus_2 {
        uint64_t _tmp2;
      };

      struct _after_expr_size_in_Times {
        const Expr *a1;
      };

      struct _after_expr_size_in_Times_2 {
        uint64_t _tmp4;
      };

      using _frame = std::variant<
          _call, _after_expr_size_in_Plus, _after_expr_size_in_Plus_2,
          _after_expr_size_in_Times, _after_expr_size_in_Times_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            _result = UINT64_C(1);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(_after_expr_size_in_Plus{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(_after_expr_size_in_Times{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_expr_size_in_Plus>(_popped)) {
          auto _f = std::move(std::get<_after_expr_size_in_Plus>(_popped));
          _stack.pop_back();
          const Expr &a1 = *_f.a1;
          _stack.emplace_back(_after_expr_size_in_Plus_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_expr_size_in_Plus_2>(_popped)) {
          auto _f = std::move(std::get<_after_expr_size_in_Plus_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp2) + std::move(_result));
        } else if (std::holds_alternative<_after_expr_size_in_Times>(_popped)) {
          auto _f = std::move(std::get<_after_expr_size_in_Times>(_popped));
          _stack.pop_back();
          const Expr &a1 = *_f.a1;
          _stack.emplace_back(_after_expr_size_in_Times_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_expr_size_in_Times_2>(_popped));
          _stack.pop_back();
          _result = ((UINT64_C(1) + _f._tmp4) + std::move(_result));
        }
      }
      return _result;
    }

    uint64_t eval() const {
      const Expr *_self = this;

      // Explicit stack replaces the non-tail recursion of eval: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const Expr *_self;
      };

      struct _after_eval_in_Plus {
        const Expr *a1;
      };

      struct _after_eval_in_Plus_2 {
        uint64_t _tmp2;
      };

      struct _after_eval_in_Times {
        const Expr *a1;
      };

      struct _after_eval_in_Times_2 {
        uint64_t _tmp4;
      };

      using _frame =
          std::variant<_call, _after_eval_in_Plus, _after_eval_in_Plus_2,
                       _after_eval_in_Times, _after_eval_in_Times_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            const auto &[a0] = std::get<typename Expr::Num>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(_after_eval_in_Plus{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(_after_eval_in_Times{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_eval_in_Plus>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Plus>(_popped));
          _stack.pop_back();
          const Expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_in_Plus_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_eval_in_Plus_2>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Plus_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 + std::move(_result));
        } else if (std::holds_alternative<_after_eval_in_Times>(_popped)) {
          auto _f = std::move(std::get<_after_eval_in_Times>(_popped));
          _stack.pop_back();
          const Expr &a1 = *_f.a1;
          _stack.emplace_back(_after_eval_in_Times_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_eval_in_Times_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp4 * std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template Expr_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const Expr *_self = this;

      // Explicit stack replaces the non-tail recursion of Expr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const Expr *_self;
      };

      struct _after_Expr_rect_in_Plus {
        std::shared_ptr<Expr> a0;
        const Expr *a1;
      };

      struct _after_Expr_rect_in_Plus_2 {
        std::shared_ptr<Expr> a0;
        const Expr *a1;
        T1 _tmp2;
      };

      struct _after_Expr_rect_in_Times {
        std::shared_ptr<Expr> a0;
        const Expr *a1;
      };

      struct _after_Expr_rect_in_Times_2 {
        std::shared_ptr<Expr> a0;
        const Expr *a1;
        T1 _tmp4;
      };

      using _frame = std::variant<
          _call, _after_Expr_rect_in_Plus, _after_Expr_rect_in_Plus_2,
          _after_Expr_rect_in_Times, _after_Expr_rect_in_Times_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const Expr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename Expr::Num>(_sv.v())) {
            const auto &[a0] = std::get<typename Expr::Num>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename Expr::Plus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename Expr::Plus>(_sv.v());
            _stack.emplace_back(_after_Expr_rect_in_Plus{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1] = std::get<typename Expr::Times>(_sv.v());
            _stack.emplace_back(_after_Expr_rect_in_Times{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_Expr_rect_in_Plus>(_popped)) {
          auto _f = std::move(std::get<_after_Expr_rect_in_Plus>(_popped));
          _stack.pop_back();
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          const Expr &a1 = *_f.a1;
          _stack.emplace_back(_after_Expr_rect_in_Plus_2{std::move(a0), &a1,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_Expr_rect_in_Plus_2>(_popped)) {
          auto _f = std::move(std::get<_after_Expr_rect_in_Plus_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          const Expr &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
        } else if (std::holds_alternative<_after_Expr_rect_in_Times>(_popped)) {
          auto _f = std::move(std::get<_after_Expr_rect_in_Times>(_popped));
          _stack.pop_back();
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          const Expr &a1 = *_f.a1;
          _stack.emplace_back(_after_Expr_rect_in_Times_2{std::move(a0), &a1,
                                                          std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_Expr_rect_in_Times_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<Expr> a0 = std::move(_f.a0);
          const Expr &a1 = *_f.a1;
          _result = f1(*a0, std::move(_f._tmp4), a1, std::move(_result));
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

    static BExpr band(crane::shared_child_slot<BExpr> a0,
                      crane::shared_child_slot<BExpr> a1) {
      return BExpr(BAnd{a0.take(), a1.take()});
    }

    static BExpr bor(crane::shared_child_slot<BExpr> a0,
                     crane::shared_child_slot<BExpr> a1) {
      return BExpr(BOr{a0.take(), a1.take()});
    }

    static BExpr bnot(crane::shared_child_slot<BExpr> a0) {
      return BExpr(BNot{a0.take()});
    }

    // MANIPULATORS
    ~BExpr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<BTrue>(v_mut())) {
        return;
      }
      if (std::holds_alternative<BFalse>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<BAnd>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<BOr>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<BNot>(&v_mut())) {
        if (!(_alt->a0 && _alt->a0.use_count() == 1)) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<BExpr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BAnd>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BOr>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<BNot>(&_v)) {
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

    BExpr(const BExpr &) = default;
    BExpr &operator=(const BExpr &) = default;
    BExpr(BExpr &&) = default;
    BExpr &operator=(BExpr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    bool beval() const {
      const BExpr *_self = this;

      // Explicit stack replaces the non-tail recursion of beval: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const BExpr *_self;
      };

      struct _after_beval_in_BAnd {
        const BExpr *a1;
      };

      struct _after_beval_in_BAnd_2 {
        bool _tmp2;
      };

      struct _after_beval_in_BNot {};

      struct _after_beval_in_BOr {
        const BExpr *a1;
      };

      struct _after_beval_in_BOr_2 {
        bool _tmp4;
      };

      using _frame = std::variant<_call, _after_beval_in_BAnd,
                                  _after_beval_in_BAnd_2, _after_beval_in_BNot,
                                  _after_beval_in_BOr, _after_beval_in_BOr_2>;
      bool _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const BExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
            _result = true;
          } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
            _result = false;
          } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BAnd>(_sv.v());
            _stack.emplace_back(_after_beval_in_BAnd{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BOr>(_sv.v());
            _stack.emplace_back(_after_beval_in_BOr{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename BExpr::BNot>(_sv.v());
            _stack.emplace_back(_after_beval_in_BNot{});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_beval_in_BAnd>(_popped)) {
          auto _f = std::move(std::get<_after_beval_in_BAnd>(_popped));
          _stack.pop_back();
          const BExpr &a1 = *_f.a1;
          _stack.emplace_back(_after_beval_in_BAnd_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_beval_in_BAnd_2>(_popped)) {
          auto _f = std::move(std::get<_after_beval_in_BAnd_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 && std::move(_result));
        } else if (std::holds_alternative<_after_beval_in_BNot>(_popped)) {
          auto _f = std::move(std::get<_after_beval_in_BNot>(_popped));
          _stack.pop_back();
          _result = !(std::move(_result));
        } else if (std::holds_alternative<_after_beval_in_BOr>(_popped)) {
          auto _f = std::move(std::get<_after_beval_in_BOr>(_popped));
          _stack.pop_back();
          const BExpr &a1 = *_f.a1;
          _stack.emplace_back(_after_beval_in_BOr_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_beval_in_BOr_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp4 || std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F2, typename F3, typename F4>
    T1 BExpr_rec(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      return this->template BExpr_rect<T1>(std::move(f), std::move(f0), f1, f2,
                                           f3);
    }

    template <typename T1, typename F2, typename F3, typename F4>
    T1 BExpr_rect(T1 f, T1 f0, F2 &&f1, F3 &&f2, F4 &&f3) const {
      const BExpr *_self = this;

      // Explicit stack replaces the non-tail recursion of BExpr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const BExpr *_self;
      };

      struct _after_BExpr_rect_in_BAnd {
        std::shared_ptr<BExpr> a0;
        const BExpr *a1;
      };

      struct _after_BExpr_rect_in_BAnd_2 {
        std::shared_ptr<BExpr> a0;
        const BExpr *a1;
        T1 _tmp2;
      };

      struct _after_BExpr_rect_in_BNot {
        std::shared_ptr<BExpr> a0;
      };

      struct _after_BExpr_rect_in_BOr {
        std::shared_ptr<BExpr> a0;
        const BExpr *a1;
      };

      struct _after_BExpr_rect_in_BOr_2 {
        std::shared_ptr<BExpr> a0;
        const BExpr *a1;
        T1 _tmp4;
      };

      using _frame =
          std::variant<_call, _after_BExpr_rect_in_BAnd,
                       _after_BExpr_rect_in_BAnd_2, _after_BExpr_rect_in_BNot,
                       _after_BExpr_rect_in_BOr, _after_BExpr_rect_in_BOr_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const BExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename BExpr::BTrue>(_sv.v())) {
            _result = f;
          } else if (std::holds_alternative<typename BExpr::BFalse>(_sv.v())) {
            _result = f0;
          } else if (std::holds_alternative<typename BExpr::BAnd>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BAnd>(_sv.v());
            _stack.emplace_back(_after_BExpr_rect_in_BAnd{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else if (std::holds_alternative<typename BExpr::BOr>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename BExpr::BOr>(_sv.v());
            _stack.emplace_back(_after_BExpr_rect_in_BOr{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0] = std::get<typename BExpr::BNot>(_sv.v());
            _stack.emplace_back(_after_BExpr_rect_in_BNot{a0});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_BExpr_rect_in_BAnd>(_popped)) {
          auto _f = std::move(std::get<_after_BExpr_rect_in_BAnd>(_popped));
          _stack.pop_back();
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          const BExpr &a1 = *_f.a1;
          _stack.emplace_back(_after_BExpr_rect_in_BAnd_2{std::move(a0), &a1,
                                                          std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else if (std::holds_alternative<_after_BExpr_rect_in_BAnd_2>(_popped)) {
          auto _f = std::move(std::get<_after_BExpr_rect_in_BAnd_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          const BExpr &a1 = *_f.a1;
          _result = f1(*a0, std::move(_f._tmp2), a1, std::move(_result));
        } else if (std::holds_alternative<_after_BExpr_rect_in_BNot>(_popped)) {
          auto _f = std::move(std::get<_after_BExpr_rect_in_BNot>(_popped));
          _stack.pop_back();
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          _result = f3(*a0, std::move(_result));
        } else if (std::holds_alternative<_after_BExpr_rect_in_BOr>(_popped)) {
          auto _f = std::move(std::get<_after_BExpr_rect_in_BOr>(_popped));
          _stack.pop_back();
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          const BExpr &a1 = *_f.a1;
          _stack.emplace_back(_after_BExpr_rect_in_BOr_2{std::move(a0), &a1,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_BExpr_rect_in_BOr_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<BExpr> a0 = std::move(_f.a0);
          const BExpr &a1 = *_f.a1;
          _result = f2(*a0, std::move(_f._tmp4), a1, std::move(_result));
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

    static AExpr aplus(crane::shared_child_slot<AExpr> a0,
                       crane::shared_child_slot<AExpr> a1) {
      return AExpr(APlus{a0.take(), a1.take()});
    }

    static AExpr aif(BExpr a0, crane::shared_child_slot<AExpr> a1,
                     crane::shared_child_slot<AExpr> a2) {
      return AExpr(AIf{std::move(a0), a1.take(), a2.take()});
    }

    // MANIPULATORS
    ~AExpr() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<ANum>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<APlus>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      if (auto *_alt = std::get_if<AIf>(&v_mut())) {
        if (!((_alt->a1 && _alt->a1.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<AExpr>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<APlus>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
        }
        if (auto *_alt = std::get_if<AIf>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
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
    AExpr(AExpr &&) = default;
    AExpr &operator=(AExpr &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t aeval() const {
      const AExpr *_self = this;

      // Explicit stack replaces the non-tail recursion of aeval: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const AExpr *_self;
      };

      struct _after_aeval_in_APlus {
        const AExpr *a1;
      };

      struct _after_aeval_in_APlus_2 {
        uint64_t _tmp2;
      };

      using _frame =
          std::variant<_call, _after_aeval_in_APlus, _after_aeval_in_APlus_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const AExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename AExpr::ANum>(_sv.v());
            _result = std::move(a0);
          } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
            const auto &[a0, a1] = std::get<typename AExpr::APlus>(_sv.v());
            _stack.emplace_back(_after_aeval_in_APlus{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          } else {
            const auto &[a0, a1, a2] = std::get<typename AExpr::AIf>(_sv.v());
            if (a0.beval()) {
              _stack.emplace_back(_call{crane_raw(a1)});
            } else {
              _stack.emplace_back(_call{crane_raw(a2)});
            }
          }
        } else if (std::holds_alternative<_after_aeval_in_APlus>(_popped)) {
          auto _f = std::move(std::get<_after_aeval_in_APlus>(_popped));
          _stack.pop_back();
          const AExpr &a1 = *_f.a1;
          _stack.emplace_back(_after_aeval_in_APlus_2{std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_aeval_in_APlus_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template AExpr_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      const AExpr *_self = this;

      // Explicit stack replaces the non-tail recursion of AExpr_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const AExpr *_self;
      };

      struct _after_AExpr_rect_in_AIf {
        BExpr a2;
        std::shared_ptr<AExpr> a3;
        const AExpr *a4;
      };

      struct _after_AExpr_rect_in_AIf_2 {
        BExpr a2;
        std::shared_ptr<AExpr> a3;
        const AExpr *a4;
        T1 _tmp4;
      };

      struct _after_AExpr_rect_in_APlus {
        std::shared_ptr<AExpr> a2;
        const AExpr *a3;
      };

      struct _after_AExpr_rect_in_APlus_2 {
        std::shared_ptr<AExpr> a2;
        const AExpr *a3;
        T1 _tmp2;
      };

      using _frame = std::variant<
          _call, _after_AExpr_rect_in_AIf, _after_AExpr_rect_in_AIf_2,
          _after_AExpr_rect_in_APlus, _after_AExpr_rect_in_APlus_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const AExpr *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename AExpr::ANum>(_sv.v())) {
            const auto &[a0] = std::get<typename AExpr::ANum>(_sv.v());
            _result = f(a0);
          } else if (std::holds_alternative<typename AExpr::APlus>(_sv.v())) {
            const auto &[a2, a3] = std::get<typename AExpr::APlus>(_sv.v());
            _stack.emplace_back(_after_AExpr_rect_in_APlus{a2, crane_raw(a3)});
            _stack.emplace_back(_call{crane_raw(a2)});
          } else {
            const auto &[a2, a3, a4] = std::get<typename AExpr::AIf>(_sv.v());
            _stack.emplace_back(_after_AExpr_rect_in_AIf{a2, a3,
                                                         crane_raw(a4)});
            _stack.emplace_back(_call{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_after_AExpr_rect_in_AIf>(_popped)) {
          auto _f = std::move(std::get<_after_AExpr_rect_in_AIf>(_popped));
          _stack.pop_back();
          BExpr a2 = std::move(_f.a2);
          std::shared_ptr<AExpr> a3 = std::move(_f.a3);
          const AExpr &a4 = *_f.a4;
          _stack.emplace_back(_after_AExpr_rect_in_AIf_2{
              std::move(a2), std::move(a3), &a4, std::move(_result)});
          _stack.emplace_back(_call{_f.a4});
        } else if (std::holds_alternative<_after_AExpr_rect_in_AIf_2>(_popped)) {
          auto _f = std::move(std::get<_after_AExpr_rect_in_AIf_2>(_popped));
          _stack.pop_back();
          BExpr a2 = std::move(_f.a2);
          std::shared_ptr<AExpr> a3 = std::move(_f.a3);
          const AExpr &a4 = *_f.a4;
          _result = f1(a2, *a3, std::move(_f._tmp4), a4, std::move(_result));
        } else if (std::holds_alternative<_after_AExpr_rect_in_APlus>(_popped)) {
          auto _f = std::move(std::get<_after_AExpr_rect_in_APlus>(_popped));
          _stack.pop_back();
          std::shared_ptr<AExpr> a2 = std::move(_f.a2);
          const AExpr &a3 = *_f.a3;
          _stack.emplace_back(_after_AExpr_rect_in_APlus_2{std::move(a2), &a3,
                                                           std::move(_result)});
          _stack.emplace_back(_call{_f.a3});
        } else {
          auto _f = std::move(std::get<_after_AExpr_rect_in_APlus_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<AExpr> a2 = std::move(_f.a2);
          const AExpr &a3 = *_f.a3;
          _result = f0(*a2, std::move(_f._tmp2), a3, std::move(_result));
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
