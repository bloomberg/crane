#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
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

    static Frame_ resume_cons_(crane::shared_child_slot<Frame_> a0) {
      return Frame_(Resume_Cons_{a0.take()});
    }

    // MANIPULATORS
    ~Frame_() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<Frame_> {
        if (auto *_alt = std::get_if<Resume_Cons_>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<Frame_> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    Frame_(const Frame_ &) = default;
    Frame_ &operator=(const Frame_ &) = default;
    Frame_(Frame_ &&) = default;
    Frame_ &operator=(Frame_ &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 Frame_rect_(F0 &&f, F1 &&f0, const Frame_ &f_) {
    // Explicit stack replaces the non-tail recursion of _Frame_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const Frame_ *f_;
    };

    struct _after_pFrame_rect_in_Resume_Cons_ {
      std::shared_ptr<Frame_> a0;
    };

    using _frame = std::variant<_call, _after_pFrame_rect_in_Resume_Cons_>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&f_});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const Frame_ &f_ = *_f.f_;
        if (std::holds_alternative<typename Frame_::Enter_>(f_.v())) {
          const auto &[a0] = std::get<typename Frame_::Enter_>(f_.v());
          _result = f(a0);
        } else {
          const auto &[a0] = std::get<typename Frame_::Resume_Cons_>(f_.v());
          _stack.emplace_back(_after_pFrame_rect_in_Resume_Cons_{a0});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else {
        auto _f =
            std::move(std::get<_after_pFrame_rect_in_Resume_Cons_>(_popped));
        _stack.pop_back();
        std::shared_ptr<Frame_> a0 = std::move(_f.a0);
        _result = f0(*a0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
  static T1 Frame_rec_(F0 &&f, F1 &&f0, const Frame_ &f_) {
    return Frame_rect_<T1>(f, f0, f_);
  }

  static uint64_t depth(const Frame_ &f);
  static Frame_ mk(uint64_t n);
  /// Definition names that become loopify's locals.
  static constexpr uint64_t stack_ = UINT64_C(1);
  static constexpr uint64_t result_ = UINT64_C(2);
  static constexpr uint64_t self_ = UINT64_C(3);
  static uint64_t locals(uint64_t n);
  static inline const uint64_t run =
      depth(mk(UINT64_C(5))) + locals(UINT64_C(10));
};
