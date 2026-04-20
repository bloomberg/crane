#ifndef INCLUDED_FIX_CAPTURE_FN_ARG
#define INCLUDED_FIX_CAPTURE_FN_ARG

#include <functional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct FixCaptureFnArg {
  /// A local fixpoint captures a FUNCTION argument AND is returned
  /// through a pair (preventing uncurrying).
  ///
  /// BUG: go uses & capture. Both f (a std::function on the
  /// caller's stack) and base are captured by reference.
  /// The fixpoint escapes through the pair — after make_transform
  /// returns, f (the std::function object), base, and the local
  /// go are all destroyed. The returned closure dereferences a
  /// destroyed std::function when it calls f.
  template <MapsTo<unsigned int, unsigned int> F0>
  __attribute__((pure)) static std::pair<
      unsigned int, std::function<unsigned int(unsigned int)>>
  make_transform(F0 &&f, const unsigned int base) {
    std::function<unsigned int(unsigned int)> go;
    go = [&](unsigned int x) -> unsigned int {
      if (x <= 0) {
        return f(base);
      } else {
        unsigned int x_ = x - 1;
        return (go(x_) + 1);
      }
    };
    return std::make_pair(f(base), go);
  }

  /// test1: make_transform(x=>x*2, 5) = (10, go).
  /// go(3) = (5*2) + 3 = 13. Total = 10 + 13 = 23.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs =
        make_transform([](const unsigned int x) { return (x * 2u); }, 5u);
    const unsigned int &n = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (n + g(3u));
  }();
  /// test2: make_transform(S, 10) = (11, go).
  /// go(5) = S(10) + 5 = 16. Total = 11 + 16 = 27.
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs =
        make_transform([](const unsigned int x) { return (x + 1); }, 10u);
    const unsigned int &n = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (n + g(5u));
  }();
};

#endif // INCLUDED_FIX_CAPTURE_FN_ARG
