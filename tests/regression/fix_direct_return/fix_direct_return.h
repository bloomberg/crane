#ifndef INCLUDED_FIX_DIRECT_RETURN
#define INCLUDED_FIX_DIRECT_RETURN

#include <functional>
#include <type_traits>

struct FixDirectReturn {
  /// A local fixpoint is captured by an outer lambda and returned.
  /// Crane can't uncurry here because the fixpoint is used as a VALUE
  /// inside the returned lambda (not fully applied at the return site).
  ///
  /// BUG: The inner fixpoint add uses & capture. Even though the
  /// outer lambda uses = capture (via return_captures_by_value),
  /// the COPY of add (a std::function) inside the outer lambda
  /// still holds & references to the destroyed stack variables.
  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t make_callback(uint64_t base, F1 &&_x0) {
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
      return [=](std::function<uint64_t(uint64_t)> g) mutable {
        return (g(add(UINT64_C(0))) + add(UINT64_C(1)));
      };
    }()(_x0);
  }

  /// test1: make_callback(42)(fun x => x) = id(42) + 43 = 85.
  static inline const uint64_t test1 =
      make_callback(UINT64_C(42), [](uint64_t x) { return x; });
  /// test2: make_callback(10)(fun x => x * 2) = 20 + 11 = 31.
  static inline const uint64_t test2 =
      make_callback(UINT64_C(10), [](uint64_t x) { return (x * UINT64_C(2)); });
  /// test3: Nested — use the closure from make_callback inside another
  /// make_callback.
  static inline const uint64_t test3 = []() {
    return []() {
      std::function<uint64_t(std::function<uint64_t(uint64_t)>)> cb1 =
          [](std::function<uint64_t(uint64_t)> _x0) -> uint64_t {
        return make_callback(UINT64_C(5), _x0);
      };
      std::function<uint64_t(std::function<uint64_t(uint64_t)>)> cb2 =
          [](std::function<uint64_t(uint64_t)> _x0) -> uint64_t {
        return make_callback(UINT64_C(100), _x0);
      };
      return cb1(
          [=](uint64_t) mutable { return cb2([](uint64_t x) { return x; }); });
    }();
  }();
};

#endif // INCLUDED_FIX_DIRECT_RETURN
