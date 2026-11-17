#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

enum class Ty;
struct Expr;
enum class Ty { TNAT, TBOOL };

struct Expr {
  // TYPES
  struct ENat {
    uint64_t a0;
  };

  struct EBool {
    bool a0;
  };

  struct EAdd {
    std::shared_ptr<Expr> a0;
    std::shared_ptr<Expr> a1;
  };

  struct EEq {
    std::shared_ptr<Expr> a0;
    std::shared_ptr<Expr> a1;
  };

  struct EIf {
    Ty t;
    std::shared_ptr<Expr> a1;
    std::shared_ptr<Expr> a2;
    std::shared_ptr<Expr> a3;
  };

  using variant_t = std::variant<ENat, EBool, EAdd, EEq, EIf>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Expr() {}

  explicit Expr(ENat _v) : v_(std::move(_v)) {}

  explicit Expr(EBool _v) : v_(std::move(_v)) {}

  explicit Expr(EAdd _v) : v_(std::move(_v)) {}

  explicit Expr(EEq _v) : v_(std::move(_v)) {}

  explicit Expr(EIf _v) : v_(std::move(_v)) {}

  static Expr enat(uint64_t a0) { return Expr(ENat{a0}); }

  static Expr ebool(bool a0) { return Expr(EBool{a0}); }

  static Expr eadd(crane::shared_child_slot<Expr> a0,
                   crane::shared_child_slot<Expr> a1) {
    return Expr(EAdd{a0.take(), a1.take()});
  }

  static Expr eeq(crane::shared_child_slot<Expr> a0,
                  crane::shared_child_slot<Expr> a1) {
    return Expr(EEq{a0.take(), a1.take()});
  }

  static Expr eif(Ty t, crane::shared_child_slot<Expr> a1,
                  crane::shared_child_slot<Expr> a2,
                  crane::shared_child_slot<Expr> a3) {
    return Expr(EIf{t, a1.take(), a2.take(), a3.take()});
  }

  // MANIPULATORS
  ~Expr() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    if (std::holds_alternative<ENat>(v_mut())) {
      return;
    }
    if (std::holds_alternative<EBool>(v_mut())) {
      return;
    }
    if (auto *_alt = std::get_if<EAdd>(&v_mut())) {
      if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
            (_alt->a1 && _alt->a1.use_count() == 1))) {
        return;
      }
    }
    if (auto *_alt = std::get_if<EEq>(&v_mut())) {
      if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
            (_alt->a1 && _alt->a1.use_count() == 1))) {
        return;
      }
    }
    if (auto *_alt = std::get_if<EIf>(&v_mut())) {
      if (!((_alt->a1 && _alt->a1.use_count() == 1) ||
            (_alt->a2 && _alt->a2.use_count() == 1) ||
            (_alt->a3 && _alt->a3.use_count() == 1))) {
        return;
      }
    }
    crane::small_vector<std::shared_ptr<Expr>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<EAdd>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
        }
      }
      if (auto *_alt = std::get_if<EEq>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
        }
      }
      if (auto *_alt = std::get_if<EIf>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          _stack.push_back(std::move(_alt->a1));
        }
        if (_alt->a2 && _alt->a2.use_count() == 1) {
          _stack.push_back(std::move(_alt->a2));
        }
        if (_alt->a3 && _alt->a3.use_count() == 1) {
          _stack.push_back(std::move(_alt->a3));
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

  crane::obj eval(Ty _x) const;
};

inline crane::obj Expr::eval(Ty _x) const {
  const Expr *_self = this;

  // Explicit stack replaces the non-tail recursion of eval: _call frames are
  // pending calls, _after frames resume a caller.
  struct _call {
    const Expr *_self;
    Ty _x;
  };

  struct _after_eval_in_EAdd {
    const Expr *a1;
  };

  struct _after_eval_in_EAdd_2 {
    crane::obj _tmp2;
  };

  struct _after_eval_in_EEq {
    const Expr *a1;
  };

  struct _after_eval_in_EEq_2 {
    crane::obj _tmp4;
  };

  struct _after_eval_in_EIf {
    Ty t;
    const Expr *a2;
    const Expr *a3;
  };

  using _frame = std::variant<_call, _after_eval_in_EAdd, _after_eval_in_EAdd_2,
                              _after_eval_in_EEq, _after_eval_in_EEq_2,
                              _after_eval_in_EIf>;
  crane::obj _result{};
  crane::small_vector<_frame> _stack;
  _stack.emplace_back(_call{_self, _x});
  while (!_stack.empty()) {
    _frame &_popped = _stack.back();
    if (std::holds_alternative<_call>(_popped)) {
      auto _f = std::move(std::get<_call>(_popped));
      _stack.pop_back();
      const Expr *_self = _f._self;
      Ty _x = _f._x;
      auto &&_sv = *_self;
      if (std::holds_alternative<typename Expr::ENat>(_sv.v())) {
        const auto &[a0] = std::get<typename Expr::ENat>(_sv.v());
        _result = std::move(a0);
      } else if (std::holds_alternative<typename Expr::EBool>(_sv.v())) {
        const auto &[a0] = std::get<typename Expr::EBool>(_sv.v());
        _result = std::move(a0);
      } else if (std::holds_alternative<typename Expr::EAdd>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename Expr::EAdd>(_sv.v());
        _stack.emplace_back(_after_eval_in_EAdd{crane_raw(a1)});
        _stack.emplace_back(_call{crane_raw(a0), Ty::TNAT});
      } else if (std::holds_alternative<typename Expr::EEq>(_sv.v())) {
        const auto &[a0, a1] = std::get<typename Expr::EEq>(_sv.v());
        _stack.emplace_back(_after_eval_in_EEq{crane_raw(a1)});
        _stack.emplace_back(_call{crane_raw(a0), Ty::TNAT});
      } else {
        const auto &[t, a1, a2, a3] = std::get<typename Expr::EIf>(_sv.v());
        _stack.emplace_back(_after_eval_in_EIf{t, crane_raw(a2),
                                               crane_raw(a3)});
        _stack.emplace_back(_call{crane_raw(a1), Ty::TBOOL});
      }
    } else if (std::holds_alternative<_after_eval_in_EAdd>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_EAdd>(_popped));
      _stack.pop_back();
      const Expr &a1 = *_f.a1;
      _stack.emplace_back(_after_eval_in_EAdd_2{std::move(_result)});
      _stack.emplace_back(_call{_f.a1, Ty::TNAT});
    } else if (std::holds_alternative<_after_eval_in_EAdd_2>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_EAdd_2>(_popped));
      _stack.pop_back();
      _result = (crane::any_cast<uint64_t>(std::move(_f._tmp2)) +
                 crane::any_cast<uint64_t>(std::move(_result)));
    } else if (std::holds_alternative<_after_eval_in_EEq>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_EEq>(_popped));
      _stack.pop_back();
      const Expr &a1 = *_f.a1;
      _stack.emplace_back(_after_eval_in_EEq_2{std::move(_result)});
      _stack.emplace_back(_call{_f.a1, Ty::TNAT});
    } else if (std::holds_alternative<_after_eval_in_EEq_2>(_popped)) {
      auto _f = std::move(std::get<_after_eval_in_EEq_2>(_popped));
      _stack.pop_back();
      _result = crane::any_cast<uint64_t>(std::move(_f._tmp4)) ==
                crane::any_cast<uint64_t>(std::move(_result));
    } else {
      auto _f = std::move(std::get<_after_eval_in_EIf>(_popped));
      _stack.pop_back();
      Ty t = _f.t;
      const Expr &a2 = *_f.a2;
      const Expr &a3 = *_f.a3;
      if (crane::any_cast<bool>(std::move(_result))) {
        _stack.emplace_back(_call{_f.a2, t});
      } else {
        _stack.emplace_back(_call{_f.a3, t});
      }
    }
  }
  return _result;
}
