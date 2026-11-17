#ifndef INCLUDED_DEEP_TAIL_RECURSION_OVERFLOW
#define INCLUDED_DEEP_TAIL_RECURSION_OVERFLOW

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct DeepTailRecursionOverflow {
  /// A three-million-link value-type chain, built by a tail recursion and
  /// consumed by a non-tail one.  Both recursions have to become loops, and the
  /// chain's destructor has to drain its own spine, or the C++ stack overflows
  /// on any one of the three.
  struct chain {
    // TYPES
    struct End_ {
      uint64_t a0;
    };

    struct Link {
      std::shared_ptr<chain> a0;
      uint64_t a1;
    };

    using variant_t = std::variant<End_, Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(End_ _v) : v_(std::move(_v)) {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    static chain end_(uint64_t a0) { return chain(End_{a0}); }

    static chain link(chain a0, uint64_t a1) {
      return chain(Link{std::make_shared<chain>(std::move(a0)), a1});
    }

    // MANIPULATORS
    ~chain() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next = [&](variant_t &_v) -> std::shared_ptr<chain> {
        if (auto *_alt = std::get_if<Link>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<chain> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) = default;
    chain &operator=(chain &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 chain_rect(F0 &&f, F1 &&f0, const chain &c) {
    // Explicit stack replaces the non-tail recursion of chain_rect: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const chain *c;
    };

    struct _after_chain_rect_in_Link {
      std::shared_ptr<chain> a0;
      uint64_t a1;
    };

    using _frame = std::variant<_call, _after_chain_rect_in_Link>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&c});
    while (!_stack.empty()) {
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        const chain &c = *_f.c;
        if (std::holds_alternative<typename chain::End_>(c.v())) {
          const auto &[a0] = std::get<typename chain::End_>(c.v());
          _result = f(a0);
        } else {
          const auto &[a0, a1] = std::get<typename chain::Link>(c.v());
          _stack.emplace_back(_after_chain_rect_in_Link{a0, a1});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_chain_rect_in_Link>(_popped));
        std::shared_ptr<chain> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        _result = f0(*a0, std::move(_result), a1);
      }
    }
    return _result;
  }

  template <typename T1, typename F0, typename F1>
  static T1 chain_rec(F0 &&f, F1 &&f0, const chain &c) {
    return chain_rect<T1>(f, f0, c);
  }

  static chain build(uint64_t n, chain acc);
  static uint64_t total_of(const chain &c);
  static inline const uint64_t deep =
      total_of(build(UINT64_C(3000000), chain::end_(UINT64_C(0))));
};

#endif // INCLUDED_DEEP_TAIL_RECURSION_OVERFLOW
