#ifndef INCLUDED_LOOPIFY_COMPUTED_SCRUTINEE_TEMP
#define INCLUDED_LOOPIFY_COMPUTED_SCRUTINEE_TEMP

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

/// Loopification bug: a raw pointer into a *computed scrutinee temporary*
/// is stored in a stack frame that outlives the temporary.
///
/// walk is non-tail recursive and matches on wrap m l, a freshly
/// computed value rather than a variable. Loopification binds it as a
/// block-scoped temporary
///
/// auto &&_sv = wrap(m, l);
///
/// and then pushes the continuation frame
///
/// _stack.emplace_back(_Enter{crane_raw(a1), m});
///
/// where a1 is a field of _sv. The frame outlives the block, so the
/// next iteration reads *_f.l after _sv (and the cell it owned) has
/// been destroyed. hd l then observes recycled heap memory: the reads
/// happen after wrap's two make_shared calls have reused the block,
/// so the wrong answer shows up even without a sanitizer.
///
/// Rocq: go n = 7*n + n*(n-1)/2. Extracted C++ under-counts for n >= 2.
/// Removing Set Crane Loopify. makes the extracted code correct.
struct LoopifyComputedScrutineeTemp {
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
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
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
  static T1 lst_rect(T1 f, F1 &&f0, const lst &l) {
    // Explicit stack replaces the non-tail recursion of lst_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const lst *l;
    };

    struct _after_lst_rect_in_Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using _frame = std::variant<_call, _after_lst_rect_in_Cons>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = f;
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_after_lst_rect_in_Cons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_lst_rect_in_Cons>(_popped));
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
  static lst wrap(uint64_t m, const lst &l);
  static uint64_t walk(uint64_t n, const lst &l);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_COMPUTED_SCRUTINEE_TEMP
