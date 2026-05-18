#ifndef INCLUDED_FIX_COMPOSE_ESCAPE
#define INCLUDED_FIX_COMPOSE_ESCAPE

#include <functional>
#include <type_traits>

struct FixComposeEscape {
  /// A local fixpoint is composed with another function.
  ///
  /// The composition fun x => g (add x) creates a lambda with =
  /// capture, but the captured add is a std::function whose internal
  /// lambda uses & capture — it holds a reference to base, a stack
  /// variable that is destroyed when compose_add returns.  The =
  /// capture copies the std::function VALUE, including its dangling
  /// & references.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t compose_add(uint64_t base, F1 &&g, uint64_t _x0) {
    return [=]() mutable {
      auto add_impl = [=](auto &_self_add, uint64_t x) mutable -> uint64_t {
        if (x <= 0) {
          return base;
        } else {
          uint64_t x_ = x - 1;
          return (_self_add(_self_add, x_) + 1);
        }
      };
      auto add = [=](uint64_t x) mutable -> uint64_t {
        return add_impl(add_impl, x);
      };
      return [=](uint64_t x) mutable { return g(add(x)); };
    }()(_x0);
  }

  /// test1: compose_add 42 id 3 = id (42 + 3) = 45
  static inline const uint64_t test1 =
      compose_add(UINT64_C(42), [](uint64_t x) { return x; }, UINT64_C(3));
  /// test2: compose_add 10 double 5 = 2 * (10 + 5) = 30
  static inline const uint64_t test2 = compose_add(
      UINT64_C(10), [](uint64_t x) { return (x * UINT64_C(2)); }, UINT64_C(5));
  /// test3: Compose two different compositions.
  /// compose_add 100 (compose_add 50 id)
  /// = fun x => (compose_add 50 id) (100 + x)
  /// = fun x => id (50 + (100 + x))
  /// = fun x => 150 + x
  /// test3 = 150 + 7 = 157
  static inline const uint64_t test3 = []() {
    std::function<uint64_t(uint64_t)> inner = [](uint64_t _x0) -> uint64_t {
      return compose_add(UINT64_C(50), [](uint64_t x) { return x; }, _x0);
    };
    return compose_add(UINT64_C(100), inner, UINT64_C(7));
  }();
};

#endif // INCLUDED_FIX_COMPOSE_ESCAPE
