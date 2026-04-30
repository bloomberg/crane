#ifndef INCLUDED_FIX_COMPOSE_ESCAPE
#define INCLUDED_FIX_COMPOSE_ESCAPE

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct FixComposeEscape {
  /// A local fixpoint is composed with another function.
  ///
  /// The composition fun x => g (add x) creates a lambda with =
  /// capture, but the captured add is a std::function whose internal
  /// lambda uses & capture — it holds a reference to base, a stack
  /// variable that is destroyed when compose_add returns.  The =
  /// capture copies the std::function VALUE, including its dangling
  /// & references.
  template <MapsTo<unsigned int, unsigned int> F1>
  static unsigned int compose_add(const unsigned int &base, F1 &&g,
                                  unsigned int _x0) {
    return [=]() mutable {
      auto add_impl = [=](auto &_self_add,
                          unsigned int x) mutable -> unsigned int {
        if (x <= 0) {
          return base;
        } else {
          unsigned int x_ = x - 1;
          return (_self_add(_self_add, x_) + 1);
        }
      };
      auto add = [=](unsigned int x) mutable -> unsigned int {
        return add_impl(add_impl, x);
      };
      return [=](const unsigned int &x) mutable { return g(add(x)); };
    }()(_x0);
  }

  /// test1: compose_add 42 id 3 = id (42 + 3) = 45
  static inline const unsigned int test1 =
      compose_add(42u, [](unsigned int x) { return x; }, 3u);
  /// test2: compose_add 10 double 5 = 2 * (10 + 5) = 30
  static inline const unsigned int test2 =
      compose_add(10u, [](const unsigned int &x) { return (x * 2u); }, 5u);
  /// test3: Compose two different compositions.
  /// compose_add 100 (compose_add 50 id)
  /// = fun x => (compose_add 50 id) (100 + x)
  /// = fun x => id (50 + (100 + x))
  /// = fun x => 150 + x
  /// test3 = 150 + 7 = 157
  static inline const unsigned int test3 = []() {
    std::function<unsigned int(unsigned int)> inner =
        [](unsigned int _x0) -> unsigned int {
      return compose_add(50u, [](unsigned int x) { return x; }, _x0);
    };
    return compose_add(100u, inner, 7u);
  }();
};

#endif // INCLUDED_FIX_COMPOSE_ESCAPE
