#ifndef INCLUDED_LOOPIFY_MUTUAL_INLINE_TEMP
#define INCLUDED_LOOPIFY_MUTUAL_INLINE_TEMP

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// KNOWN BUG: use-after-free from loopifying mutual recursion.
///
/// even_step and odd_step are mutually tail recursive. Loopification
/// turns each into a single loop by inlining one step of its partner. The
/// partner's list argument is a freshly built value, so it is materialised as
/// a block-scoped temporary bound to a const reference:
///
/// const lst &_inl_l = lst::cons(a0 + 1, lst::nil());
/// ...
/// const auto &a0, a1 = std::get<Cons>(_inl_l.v());
/// _loop_s    = _inl_s + a0;
/// _loop_keep = crane_raw(a1);        // points INTO the temporary
/// _loop_l    = lst::cons(a0, lst::cons(a0, lst::nil()));
/// _loop_n    = m;
///
/// _loop_keep is published out of the loop body while pointing at a cell
/// owned solely by _inl_l. Lifetime extension only keeps that temporary
/// alive to the end of the enclosing block, so it dies at the end of the
/// iteration and _loop_keep dangles before the next iteration reads it
/// through hd.
///
/// Expected: go 8 = 16, go 7 = 12 (checked with Compute in Rocq).
/// Actual:   go 8 returns 12, plus an ASan heap-use-after-free.
///
/// Without Set Crane Loopify the same file extracts to correct code.
struct LoopifyMutualInlineTemp {
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
          std::atomic_thread_fence(std::memory_order_acquire);
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

  static lst build(uint64_t n, lst acc);
  static uint64_t hd(const lst &l);
  static uint64_t even_step(uint64_t n, const lst &l, const lst &keep,
                            uint64_t s);
  static uint64_t odd_step(uint64_t n, const lst &l, const lst &keep,
                           uint64_t s);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_MUTUAL_INLINE_TEMP
