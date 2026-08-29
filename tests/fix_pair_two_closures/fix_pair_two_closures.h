#ifndef INCLUDED_FIX_PAIR_TWO_CLOSURES
#define INCLUDED_FIX_PAIR_TWO_CLOSURES

#include <functional>
#include <utility>

struct FixPairTwoClosures {
  static std::pair<std::function<uint64_t(uint64_t)>,
                   std::function<uint64_t(uint64_t)>>
  make_ops(uint64_t a, uint64_t b);
  static inline const uint64_t test1 = []() -> uint64_t {
    auto [f, g] = make_ops(UINT64_C(10), UINT64_C(20));
    return (f(UINT64_C(3)) + g(UINT64_C(5)));
  }();
  static inline const uint64_t test2 = []() -> uint64_t {
    auto [f, g] = make_ops(UINT64_C(10), UINT64_C(20));
    return ((f(UINT64_C(1)) + g(UINT64_C(2))) + f(UINT64_C(3)));
  }();
  static inline const uint64_t test3 = []() -> uint64_t {
    auto [f, g] = make_ops(UINT64_C(100), UINT64_C(1));
    return (f(UINT64_C(0)) + g(UINT64_C(0)));
  }();
};

#endif // INCLUDED_FIX_PAIR_TWO_CLOSURES
