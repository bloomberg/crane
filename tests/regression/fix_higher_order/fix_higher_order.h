#ifndef INCLUDED_FIX_HIGHER_ORDER
#define INCLUDED_FIX_HIGHER_ORDER

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct FixHigherOrder {
  /// A wrapper function that takes a function and stores it in Some.
  template <MapsTo<unsigned int, unsigned int> F0>
  static std::optional<std::function<unsigned int(unsigned int)>>
  wrap_fn(F0 &&f) {
    return std::make_optional<std::function<unsigned int(unsigned int)>>(f);
  }

  /// Creates a fixpoint and passes it through wrap_fn.
  /// The fixpoint escapes through the function call, not through
  /// direct constructor application.
  ///
  /// BUG HYPOTHESIS: When the fixpoint is passed as an argument to
  /// wrap_fn, the translation may use & capture. wrap_fn stores
  /// it in Some and returns. After make_wrapped returns, the
  /// captured base is destroyed.
  static std::optional<std::function<unsigned int(unsigned int)>>
  make_wrapped(unsigned int base);
  /// test1: make_wrapped(5) -> Some(go), go(3) = 5+3 = 8.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_wrapped(5u);
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(3u);
    } else {
      return 999u;
    }
  }();
  /// test2: with noise between creation and use.
  static inline const unsigned int test2 = []() {
    std::optional<std::function<unsigned int(unsigned int)>> o =
        make_wrapped(42u);
    unsigned int noise = ((((1u + 2u) + 3u) + 4u) + 5u);
    if (o.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *o;
      return (f(10u) + noise);
    } else {
      return 999u;
    }
  }();

  /// Two layers of wrapping: fixpoint passed through two functions.
  template <MapsTo<unsigned int, unsigned int> F0>
  static std::optional<std::optional<std::function<unsigned int(unsigned int)>>>
  double_wrap(F0 &&f) {
    return std::make_optional<
        std::optional<std::function<unsigned int(unsigned int)>>>(
        std::make_optional<std::function<unsigned int(unsigned int)>>(f));
  }

  static std::optional<std::optional<std::function<unsigned int(unsigned int)>>>
  make_double_wrapped(unsigned int base);
  /// test3: Doubly wrapped fixpoint. go(7) = 100+7 = 107.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_double_wrapped(100u);
    if (_cs.has_value()) {
      const std::optional<std::function<unsigned int(unsigned int)>> &o = *_cs;
      if (o.has_value()) {
        const std::function<unsigned int(unsigned int)> &f = *o;
        return f(7u);
      } else {
        return 999u;
      }
    } else {
      return 999u;
    }
  }();
};

#endif // INCLUDED_FIX_HIGHER_ORDER
