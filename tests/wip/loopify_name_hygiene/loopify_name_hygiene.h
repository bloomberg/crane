#ifndef INCLUDED_LOOPIFY_NAME_HYGIENE
#define INCLUDED_LOOPIFY_NAME_HYGIENE

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Loopification invents C++ names -- the frame structs _Enter and
/// _Resume_<Ctor>, and the locals _stack, _result, _self -- without
/// checking whether the Rocq source already spells them.  A program that does
/// is miscompiled: the generated names capture the user's, and the loop body
/// reads the frame stack where it meant to read a constant.
struct LoopifyNameHygiene {
  /// Constructor names that become loopify's frame structs.
  struct _Frame {
    // TYPES
    struct _Enter {
      uint64_t a0;
    };

    struct _Resume_Cons {
      std::shared_ptr<_Frame> a0;
    };

    using variant_t = std::variant<_Enter, _Resume_Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    _Frame() {}

    explicit _Frame(_Enter _v) : v_(std::move(_v)) {}

    explicit _Frame(_Resume_Cons _v) : v_(std::move(_v)) {}

    static _Frame _enter(uint64_t a0) { return _Frame(_Enter{a0}); }

    static _Frame _resume_cons(_Frame a0) {
      return _Frame(_Resume_Cons{std::make_shared<_Frame>(std::move(a0))});
    }

    // MANIPULATORS
    ~_Frame() {
      crane::small_vector<std::shared_ptr<_Frame>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<_Resume_Cons>(&_v)) {
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

    _Frame(const _Frame &) = default;
    _Frame &operator=(const _Frame &) = default;
    _Frame(_Frame &&) noexcept = default;
    _Frame &operator=(_Frame &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, _Frame &, T1 &>
  static T1
  _Frame_rect(F0 &&f, F1 &&f0,
              const _Frame &_f) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const _Frame *_f;
    };

    /// _Resume__Resume_Cons: saves [a0], resumes after recursive call with
    /// _result.
    struct _Resume__Resume_Cons {
      _Frame a0;
    };

    using _Frame = std::variant<_Enter, _Resume__Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&_f});
    /// Loopified _Frame_rect: _Enter -> _Resume__Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const _Frame &_f = *_f._f;
        if (std::holds_alternative<typename _Frame::_Enter>(_f.v())) {
          const auto &[a0] = std::get<typename _Frame::_Enter>(_f.v());
          _result = f(a0);
        } else {
          const auto &[a0] = std::get<typename _Frame::_Resume_Cons>(_f.v());
          _stack.emplace_back(_Resume__Resume_Cons{*a0});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_Resume__Resume_Cons>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, _Frame &, T1 &>
  static T1
  _Frame_rec(F0 &&f, F1 &&f0,
             const _Frame &_f) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const _Frame *_f;
    };

    /// _Resume__Resume_Cons: saves [a0], resumes after recursive call with
    /// _result.
    struct _Resume__Resume_Cons {
      _Frame a0;
    };

    using _Frame = std::variant<_Enter, _Resume__Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&_f});
    /// Loopified _Frame_rec: _Enter -> _Resume__Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const _Frame &_f = *_f._f;
        if (std::holds_alternative<typename _Frame::_Enter>(_f.v())) {
          const auto &[a0] = std::get<typename _Frame::_Enter>(_f.v());
          _result = f(a0);
        } else {
          const auto &[a0] = std::get<typename _Frame::_Resume_Cons>(_f.v());
          _stack.emplace_back(_Resume__Resume_Cons{*a0});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_Resume__Resume_Cons>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t depth(const _Frame &f);
  static _Frame mk(uint64_t n);
  /// Definition names that become loopify's locals.
  static inline const uint64_t _stack = UINT64_C(1);
  static inline const uint64_t _result = UINT64_C(2);
  static inline const uint64_t _self = UINT64_C(3);
  static uint64_t locals(uint64_t n);
  static inline const uint64_t run =
      (depth(mk(UINT64_C(5))) + locals(UINT64_C(10)));
};

#endif // INCLUDED_LOOPIFY_NAME_HYGIENE
