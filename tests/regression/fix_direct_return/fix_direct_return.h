#ifndef INCLUDED_FIX_DIRECT_RETURN
#define INCLUDED_FIX_DIRECT_RETURN

#include <functional>
#include <memory>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct FixDirectReturn {
  /// A local fixpoint is captured by an outer lambda and returned.
  /// Crane can't uncurry here because the fixpoint is used as a VALUE
  /// inside the returned lambda (not fully applied at the return site).
  ///
  /// BUG: The inner fixpoint add uses & capture. Even though the
  /// outer lambda uses = capture (via return_captures_by_value),
  /// the COPY of add (a std::function) inside the outer lambda
  /// still holds & references to the destroyed stack variables.
  template <MapsTo<unsigned int, unsigned int> F1>
  __attribute__((pure)) static unsigned int
  make_callback(const unsigned int base, F1 &&_x0) {
    return [&]() {
      auto add = std::make_shared<std::function<unsigned int(unsigned int)>>();
      *add = [=](unsigned int x) mutable -> unsigned int {
        if (x <= 0) {
          return base;
        } else {
          unsigned int x_ = x - 1;
          return ((*add)(x_) + 1);
        }
      };
      return [=](const std::function<unsigned int(unsigned int)> g) mutable {
        return (g((*add)(0u)) + (*add)(1u));
      };
    }()(_x0);
  }

  /// test1: make_callback(42)(fun x => x) = id(42) + 43 = 85.
  static inline const unsigned int test1 =
      make_callback(42u, [](const unsigned int x) { return x; });
  /// test2: make_callback(10)(fun x => x * 2) = 20 + 11 = 31.
  static inline const unsigned int test2 =
      make_callback(10u, [](const unsigned int x) { return (x * 2u); });
  /// test3: Nested — use the closure from make_callback inside another
  /// make_callback.
  static inline const unsigned int test3 = []() {
    return []() {
      std::function<unsigned int(std::function<unsigned int(unsigned int)>)>
          cb1 = [](std::function<unsigned int(unsigned int)> _x0)
          -> unsigned int { return make_callback(5u, _x0); };
      std::function<unsigned int(std::function<unsigned int(unsigned int)>)>
          cb2 = [](std::function<unsigned int(unsigned int)> _x0)
          -> unsigned int { return make_callback(100u, _x0); };
      return cb1([=](const unsigned int) mutable {
        return cb2([](const unsigned int x) { return x; });
      });
    }();
  }();
};

#endif // INCLUDED_FIX_DIRECT_RETURN
