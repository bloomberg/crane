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

struct InnerFixCapturesFn {
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

    static lst cons(uint64_t a0, crane::shared_child_slot<lst> a1) {
      return lst(Cons{a0, a1.take()});
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
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
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
        _stack.pop_back();
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

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &> &&
             std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t walk(F0 &&f, const lst &l) {
    // Explicit stack replaces the non-tail recursion of walk: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const lst *l;
    };

    struct _after_walk_in_Cons {
      uint64_t a0;
      std::shared_ptr<lst> a1;
    };

    using _frame = std::variant<_call, _after_walk_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&l});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const lst &l = *_f.l;
        if (std::holds_alternative<typename lst::Nil>(l.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename lst::Cons>(l.v());
          _stack.emplace_back(_after_walk_in_Cons{a0, a1});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_walk_in_Cons>(_popped));
        _stack.pop_back();
        uint64_t a0 = _f.a0;
        std::shared_ptr<lst> a1 = std::move(_f.a1);
        _result = [&]() {
          auto inner = [&](const lst &m, uint64_t a) -> uint64_t {
            // Loop replaces the tail recursion: each recursive call updates the
            // loop variables.
            const lst *_loop_m = &m;
            while (true) {
              if (std::holds_alternative<typename lst::Nil>(_loop_m->v())) {
                return a;
              } else {
                const auto &[a2, a3] =
                    std::get<typename lst::Cons>(_loop_m->v());
                a = a + f(a2);
                _loop_m = crane_raw(a3);
              }
            }
          };
          return inner(*a1, f(a0));
        }() + _result;
      }
    }
    return _result;
  }

  static lst mk(uint64_t n);
  static uint64_t go(uint64_t n);
};
