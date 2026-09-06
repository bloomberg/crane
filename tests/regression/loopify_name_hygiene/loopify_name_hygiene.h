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
  struct Frame_ {
    // TYPES
    struct Enter_ {
      uint64_t a0;
    };

    struct Resume_Cons_ {
      std::shared_ptr<Frame_> a0;
    };

    using variant_t = std::variant<Enter_, Resume_Cons_>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    Frame_() {}

    explicit Frame_(Enter_ _v) : v_(std::move(_v)) {}

    explicit Frame_(Resume_Cons_ _v) : v_(std::move(_v)) {}

    static Frame_ enter_(uint64_t a0) { return Frame_(Enter_{a0}); }

    static Frame_ resume_cons_(Frame_ a0) {
      return Frame_(Resume_Cons_{std::make_shared<Frame_>(std::move(a0))});
    }

    // MANIPULATORS
    ~Frame_() {
      crane::small_vector<std::shared_ptr<Frame_>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Resume_Cons_>(&_v)) {
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

    Frame_(const Frame_ &) = default;
    Frame_ &operator=(const Frame_ &) = default;
    Frame_(Frame_ &&) noexcept = default;
    Frame_ &operator=(Frame_ &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, Frame_ &, T1 &>
  static T1
  Frame_rect_(F0 &&f, F1 &&f0,
              const Frame_ &f_) { /// _Enter: captures varying parameters for
                                  /// each recursive call.

    struct _Enter {
      const Frame_ *f_;
    };

    /// _Resume_Resume_Cons_: saves [a0], resumes after recursive call with
    /// _result.
    struct _Resume_Resume_Cons_ {
      Frame_ a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Resume_Cons_>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&f_});
    /// Loopified _Frame_rect: _Enter -> _Resume_Resume_Cons_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const Frame_ &f_ = *_f.f_;
        if (std::holds_alternative<typename Frame_::Enter_>(f_.v())) {
          const auto &[a0] = std::get<typename Frame_::Enter_>(f_.v());
          _result = f(a0);
        } else {
          const auto &[a0] = std::get<typename Frame_::Resume_Cons_>(f_.v());
          _stack.emplace_back(_Resume_Resume_Cons_{*a0});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Resume_Cons_>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, Frame_ &, T1 &>
  static T1
  Frame_rec_(F0 &&f, F1 &&f0,
             const Frame_ &f_) { /// _Enter: captures varying parameters for
                                 /// each recursive call.

    struct _Enter {
      const Frame_ *f_;
    };

    /// _Resume_Resume_Cons_: saves [a0], resumes after recursive call with
    /// _result.
    struct _Resume_Resume_Cons_ {
      Frame_ a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Resume_Cons_>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&f_});
    /// Loopified _Frame_rec: _Enter -> _Resume_Resume_Cons_.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const Frame_ &f_ = *_f.f_;
        if (std::holds_alternative<typename Frame_::Enter_>(f_.v())) {
          const auto &[a0] = std::get<typename Frame_::Enter_>(f_.v());
          _result = f(a0);
        } else {
          const auto &[a0] = std::get<typename Frame_::Resume_Cons_>(f_.v());
          _stack.emplace_back(_Resume_Resume_Cons_{*a0});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Resume_Cons_>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result));
      }
    }
    return _result;
  }

  static uint64_t depth(const Frame_ &f);
  static Frame_ mk(uint64_t n);
  /// Definition names that become loopify's locals.
  static inline const uint64_t stack_ = UINT64_C(1);
  static inline const uint64_t result_ = UINT64_C(2);
  static inline const uint64_t self_ = UINT64_C(3);
  static uint64_t locals(uint64_t n);
  static inline const uint64_t run =
      (depth(mk(UINT64_C(5))) + locals(UINT64_C(10)));
};

#endif // INCLUDED_LOOPIFY_NAME_HYGIENE
