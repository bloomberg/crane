#ifndef INCLUDED_LOOPIFY_VARIANT_SELF_ASSIGN
#define INCLUDED_LOOPIFY_VARIANT_SELF_ASSIGN

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
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
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      std::shared_ptr<lst> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) = default;
    lst &operator=(lst &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, lst &, T1 &>
  static T1 lst_rect(T1 f, F1 &&f0, F2 &&f1,
                     const lst &l) { /// CraneEnter: captures varying parameters
                                     /// for each recursive call.

    struct CraneEnter {
      const lst *l;
    };

    /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified lst_rect: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else if (std::holds_alternative<typename lst::One>(l.v())) {
          const auto &[a0] = std::get<typename lst::One>(l.v());
          _result = f0(a0);
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        std::shared_ptr<lst> a1 = std::move(_f.a1);
        _result = f1(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1, typename F2>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F2 &, uint64_t &, lst &, T1 &>
  static T1 lst_rec(T1 f, F1 &&f0, F2 &&f1,
                    const lst &l) { /// CraneEnter: captures varying parameters
                                    /// for each recursive call.

    struct CraneEnter {
      const lst *l;
    };

    /// CraneCont_Cons: saves [a0, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using CraneFrame = std::variant<CraneEnter, CraneCont_Cons>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&l});
    /// Loopified lst_rec: CraneEnter -> CraneCont_Cons.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else if (std::holds_alternative<typename lst::One>(l.v())) {
          const auto &[a0] = std::get<typename lst::One>(l.v());
          _result = f0(a0);
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        std::shared_ptr<lst> a1 = std::move(_f.a1);
        _result = f1(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t drain(uint64_t n, const lst &l, uint64_t s);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_VARIANT_SELF_ASSIGN
