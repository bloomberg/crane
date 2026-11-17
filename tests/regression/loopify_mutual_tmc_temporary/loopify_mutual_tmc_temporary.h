#pragma once

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

/// Tail modulo cons through a partner's body.
///
/// eb's tail call to ea continues in ea's body, where ea calls eb
/// under the constructor Su: eb is lowered tail modulo cons.  Normalize
/// binds that call to a temporary, which Loopify puts back before reading
/// the constructor around it, knowing a temporary by its name.  Inlining
/// ea renamed every local of its body, the temporary too, so it was not
/// put back, the transform found no constructor around the call and left it
/// a call, and under CRANE_CHECK_IR the plan's chains were contradicted.
/// db meets the same through da's match on an enum.
struct LoopifyMutualTmcTemporary {
  struct num {
    // TYPES
    struct Z {};

    struct Su {
      std::shared_ptr<num> n;
    };

    using variant_t = std::variant<Z, Su>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    num() {}

    explicit num(Z _v) : v_(_v) {}

    explicit num(Su _v) : v_(std::move(_v)) {}

    static num z() { return num(Z{}); }

    static num su(crane::shared_child_slot<num> n) { return num(Su{n.take()}); }

    // MANIPULATORS
    ~num() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<num> {
        if (auto *_alt = std::get_if<Su>(&_v)) {
          if (_alt->n && _alt->n.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->n);
          }
        }
        return nullptr;
      };
      std::shared_ptr<num> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    num(const num &) = default;
    num &operator=(const num &) = default;
    num(num &&) = default;
    num &operator=(num &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 num_rect(T1 f, F1 &&f0, const num &n) {
    // Explicit stack replaces the non-tail recursion of num_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const num *n;
    };

    struct _after_num_rect_in_Su {
      std::shared_ptr<num> n1;
    };

    using _frame = std::variant<_call, _after_num_rect_in_Su>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&n});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const num &n = *_f.n;
        if (std::holds_alternative<typename num::Z>(n.v())) {
          _result = f;
        } else {
          const auto &[n1] = std::get<typename num::Su>(n.v());
          _stack.emplace_back(_after_num_rect_in_Su{n1});
          _stack.emplace_back(_call{crane_raw(n1)});
        }
      } else {
        auto _f = std::move(std::get<_after_num_rect_in_Su>(_popped));
        _stack.pop_back();
        std::shared_ptr<num> n1 = std::move(_f.n1);
        _result = f0(*n1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 num_rec(T1 f, F1 &&f0, const num &n) {
    return num_rect<T1>(std::move(f), f0, n);
  }

  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
    return color_rect<T1>(std::move(f), std::move(f0), std::move(f1), c);
  }

  static num ea(const num &n);
  static num eb(const num &n, num x);
  static num da(Color c, const num &n);
  static num db(const num &n);
  static num of_nat(uint64_t n);
  static uint64_t to_nat(const num &n);
  static uint64_t run_ea(uint64_t n);
  static uint64_t run_eb(uint64_t n, uint64_t x);
  static uint64_t run_da(Color c, uint64_t n);
  static uint64_t run_db(uint64_t n);
};
