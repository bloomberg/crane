#ifndef INCLUDED_FIX_PAIR_TWO_CLOSURES
#define INCLUDED_FIX_PAIR_TWO_CLOSURES

#include <functional>
#include <utility>

struct FixPairTwoClosures {
  /// Two local fixpoints escape through a pair.
  ///
  /// BUG: Both f and g use & capture. They capture a, b,
  /// and each other's std::function variables. All captured references
  /// dangle after make_ops returns.
  static std::pair<std::function<uint64_t(uint64_t)>,
                   std::function<uint64_t(uint64_t)>>
  make_ops(uint64_t a, uint64_t b);
  /// test1: make_ops(10, 20). fst(3) = 10+3 = 13, snd(5) = 20+5 = 25.
  /// Total = 38.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto _cs = make_ops(UINT64_C(10), UINT64_C(20));
    std::function<uint64_t(uint64_t)> f = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> g = std::move(_cs.second);
    return (f(UINT64_C(3)) + g(UINT64_C(5)));
  }();
  /// test2: Use both closures interleaved.
  /// fst(1) + snd(2) + fst(3) = 11 + 22 + 13 = 46.
  static inline const uint64_t test2 = []() -> uint64_t {
    auto _cs = make_ops(UINT64_C(10), UINT64_C(20));
    std::function<uint64_t(uint64_t)> f = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> g = std::move(_cs.second);
    return ((f(UINT64_C(1)) + g(UINT64_C(2))) + f(UINT64_C(3)));
  }();
  /// test3: Asymmetric arguments to stress different captured values.
  /// make_ops(100, 1). fst(0) + snd(0) = 100 + 1 = 101.
  static inline const uint64_t test3 = []() -> uint64_t {
    auto _cs = make_ops(UINT64_C(100), UINT64_C(1));
    std::function<uint64_t(uint64_t)> f = std::move(_cs.first);
    std::function<uint64_t(uint64_t)> g = std::move(_cs.second);
    return (f(UINT64_C(0)) + g(UINT64_C(0)));
  }();
};

#endif // INCLUDED_FIX_PAIR_TWO_CLOSURES
