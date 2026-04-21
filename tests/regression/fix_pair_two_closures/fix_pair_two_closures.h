#ifndef INCLUDED_FIX_PAIR_TWO_CLOSURES
#define INCLUDED_FIX_PAIR_TWO_CLOSURES

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct FixPairTwoClosures {
  /// Two local fixpoints escape through a pair.
  ///
  /// BUG: Both f and g use & capture. They capture a, b,
  /// and each other's std::function variables. All captured references
  /// dangle after make_ops returns.
  __attribute__((
      pure)) static std::pair<std::function<unsigned int(unsigned int)>,
                              std::function<unsigned int(unsigned int)>>
  make_ops(const unsigned int a, const unsigned int b);
  /// test1: make_ops(10, 20). fst(3) = 10+3 = 13, snd(5) = 20+5 = 25.
  /// Total = 38.
  static inline const unsigned int test1 = []() -> unsigned int {
    auto _cs = make_ops(10u, 20u);
    const std::function<unsigned int(unsigned int)> &f = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (f(3u) + g(5u));
  }();
  /// test2: Use both closures interleaved.
  /// fst(1) + snd(2) + fst(3) = 11 + 22 + 13 = 46.
  static inline const unsigned int test2 = []() -> unsigned int {
    auto _cs = make_ops(10u, 20u);
    const std::function<unsigned int(unsigned int)> &f = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return ((f(1u) + g(2u)) + f(3u));
  }();
  /// test3: Asymmetric arguments to stress different captured values.
  /// make_ops(100, 1). fst(0) + snd(0) = 100 + 1 = 101.
  static inline const unsigned int test3 = []() -> unsigned int {
    auto _cs = make_ops(100u, 1u);
    const std::function<unsigned int(unsigned int)> &f = _cs.first;
    const std::function<unsigned int(unsigned int)> &g = _cs.second;
    return (f(0u) + g(0u));
  }();
};

#endif // INCLUDED_FIX_PAIR_TWO_CLOSURES
