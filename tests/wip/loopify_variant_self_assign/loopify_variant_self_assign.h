#ifndef INCLUDED_LOOPIFY_VARIANT_SELF_ASSIGN
#define INCLUDED_LOOPIFY_VARIANT_SELF_ASSIGN

#include "crane_fn.h"
#include "small_vector.h"
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// KNOWN BUG: self-assignment of a loop variable from its own sub-field.
///
/// drain is tail recursive. One branch passes a freshly built list, so the
/// loop variable for l has to be an owning value rather than a pointer; the
/// other branch passes the scrutinee's own tail, which loopification emits as
/// a direct self-assignment:
///
/// const auto &a0, a1 = std::get<Cons>(_loop_l.v());
/// _loop_s  = _loop_s + a0;
/// _loop_l  = *a1;        // source is owned by _loop_l itself
///
/// _loop_l is the sole owner of the cell a1 points at, so the assignment
/// destroys its own source. When the source cell uses a *different*
/// constructor than the destination (One vs Cons), std::variant's
/// assignment path is destroy-then-construct: it runs ~Cons, which drops
/// the last shared_ptr to the One cell, and then copy-constructs One out
/// of the freed cell.
///
/// A three-constructor inductive is what makes this visible: with only two
/// constructors the surviving alternative is the empty Nil, so nothing is
/// read back out of the freed storage.
///
/// Expected: go 8 = 20, go 12 = 42 (checked with Compute in Rocq).
/// Actual:   both return 2, plus an ASan heap-use-after-free.
///
/// Without Set Crane Loopify the same file extracts to correct code.
struct LoopifyVariantSelfAssign {
  struct lst {
    // TYPES
    struct Nil {};

    struct One {
      uint64_t a0;
    };

    struct Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using variant_t = std::variant<Nil, One, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(One _v) : v_(std::move(_v)) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    static lst nil() { return lst(Nil{}); }

    static lst one(uint64_t a0) { return lst(One{a0}); }

    static lst cons(uint64_t a0, lst a1) {
      return lst(Cons{a0, std::make_shared<lst>(std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      crane::small_vector<std::shared_ptr<lst>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
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
          _drain(_cur->v_mut());
        }
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) noexcept = default;
    lst &operator=(lst &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, lst &, T1 &>
  static T1 lst_rect(T1 f, F1 &&f0, F2 &&f1,
                     const lst &l) { /// _Enter: captures varying parameters for
                                     /// each recursive call.

    struct _Enter {
      const lst *l;
    };

    /// _Resume_Cons: saves [a1, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      lst a1;
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l});
    /// Loopified lst_rect: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else if (std::holds_alternative<typename lst::One>(l.v())) {
          const auto &[a0] = std::get<typename lst::One>(l.v());
          _result = f0(a0);
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{*a1, a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f1(_f.a0, std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, lst &, T1 &>
  static T1 lst_rec(T1 f, F1 &&f0, F2 &&f1,
                    const lst &l) { /// _Enter: captures varying parameters for
                                    /// each recursive call.

    struct _Enter {
      const lst *l;
    };

    /// _Resume_Cons: saves [a1, a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      lst a1;
      uint64_t a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&l});
    /// Loopified lst_rec: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else if (std::holds_alternative<typename lst::One>(l.v())) {
          const auto &[a0] = std::get<typename lst::One>(l.v());
          _result = f0(a0);
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{*a1, a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f1(_f.a0, std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t drain(uint64_t n, const lst &l, uint64_t s);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_VARIANT_SELF_ASSIGN
