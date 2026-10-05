#ifndef INCLUDED_FIX_COMPOSE_ESCAPE
#define INCLUDED_FIX_COMPOSE_ESCAPE

#include "fn.h"
#include <cstdint>

struct FixComposeEscape {
  /// A local fixpoint is composed with another function.
  ///
  /// The composition fun x => g (add x) creates a lambda with =
  /// capture, but the captured add is a std::function whose internal
  /// lambda uses & capture — it holds a reference to base, a stack
  /// variable that is destroyed when compose_add returns.  The =
  /// capture copies the std::function VALUE, including its dangling
  /// & references.
  static uint64_t compose_add(uint64_t base, crane::fn<uint64_t(uint64_t)> g,
                              uint64_t x0_) {
    auto add_impl = [&](auto &_self_add, uint64_t x) -> uint64_t {
      if (x <= 0) {
        return base;
      } else {
        uint64_t x_ = x - 1;
        return (_self_add(_self_add, x_) + 1);
      }
    };
    auto add = [&](uint64_t x) -> uint64_t { return add_impl(add_impl, x); };
    return g(add(x0_));
  }

  /// test1: compose_add 42 id 3 = id (42 + 3) = 45
  static constexpr uint64_t test1 = UINT64_C(45);
  /// test2: compose_add 10 double 5 = 2 * (10 + 5) = 30
  static constexpr uint64_t test2 = UINT64_C(30);
  /// test3: Compose two different compositions.
  /// compose_add 100 (compose_add 50 id)
  /// = fun x => (compose_add 50 id) (100 + x)
  /// = fun x => id (50 + (100 + x))
  /// = fun x => 150 + x
  /// test3 = 150 + 7 = 157
  static constexpr uint64_t test3 = UINT64_C(157);
};

#endif // INCLUDED_FIX_COMPOSE_ESCAPE
