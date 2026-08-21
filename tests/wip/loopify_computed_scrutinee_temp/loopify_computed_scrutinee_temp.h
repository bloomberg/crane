#ifndef INCLUDED_LOOPIFY_COMPUTED_SCRUTINEE_TEMP
#define INCLUDED_LOOPIFY_COMPUTED_SCRUTINEE_TEMP

#include "crane_fn.h"
#include "small_vector.h"
#include <memory>
#include <type_traits>
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

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
  static T1 lst_rect(T1 f, F1 &&f0,
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
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{*a1, a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, uint64_t &, lst &, T1 &>
  static T1 lst_rec(T1 f, F1 &&f0,
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
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_Resume_Cons{*a1, a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f0(_f.a0, std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t hd(const lst &l);
  static lst wrap(uint64_t m, lst l);
  static uint64_t walk(uint64_t n, const lst &l);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_COMPUTED_SCRUTINEE_TEMP
