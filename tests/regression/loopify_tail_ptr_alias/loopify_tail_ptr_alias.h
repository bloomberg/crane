#ifndef INCLUDED_LOOPIFY_TAIL_PTR_ALIAS
#define INCLUDED_LOOPIFY_TAIL_PTR_ALIAS

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

/// KNOWN BUG: use-after-free in a loopified tail-recursive function.
///
/// rot is tail recursive in two list arguments. Loopification picks a
/// different representation for each loop variable:
///
/// - acc is only ever passed on as a sub-field of the scrutinee, so it
/// becomes a raw pointer:      const lst *_loop_acc
/// - l is sometimes given a freshly built value, so it becomes an owning
/// value:                      lst _loop_l
///
/// The generated loop body is
///
/// const auto &a0, a1 = std::get<Cons>(_loop_l.v());
/// const lst *_next_acc = crane_raw(a1);                 // points INTO _loop_l
/// _loop_s = _loop_s + hd(deref _loop_acc);
/// _loop_l = lst::cons(0, lst::cons(m, lst::nil()));     // frees the old
/// _loop_l _loop_acc = _next_acc;                                // now
/// dangling
///
/// _next_acc aliases the tail cell owned by _loop_l. Overwriting
/// _loop_l drops the last shared_ptr to that cell, so the pointer
/// published into _loop_acc is dangling before the next iteration reads it
/// through hd.
///
/// Expected: go 6 = 21 (checked with Compute in Rocq).
/// Actual:   7, plus an ASan heap-use-after-free.
///
/// Without Set Crane Loopify the same file extracts to correct code.
struct LoopifyTailPtrAlias {
  struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    static lst nil() { return lst(Nil{}); }

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

  template <typename T1, typename F1>
  static T1 lst_rect(T1 f, F1 &&f0,
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
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(CraneCont_Cons{a0, a1});
          _stack.emplace_back(CraneEnter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<CraneCont_Cons>(_frame));
        uint64_t a0 = _f.a0;
        std::shared_ptr<lst> a1 = std::move(_f.a1);
        _result = f0(a0, *a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 lst_rec(T1 f, F1 &&f0, const lst &l) {
    return lst_rect<T1>(std::move(f), f0, l);
  }

  static uint64_t hd(const lst &l);
  static uint64_t rot(uint64_t n, const lst &l, const lst &acc, uint64_t s);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_TAIL_PTR_ALIAS
