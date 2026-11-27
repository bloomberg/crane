#pragma once

#include "fn.h"
#include <cstdint>
#include <utility>

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
  static std::pair<uint64_t, crane::fn<uint64_t(uint64_t)>>
  make_transform(crane::fn<uint64_t(uint64_t)> f, uint64_t base);
  /// test1: make_transform(x=>x*2, 5) = (10, go).
  /// go(3) = (5*2) + 3 = 13. Total = 10 + 13 = 23.
  static inline const uint64_t test1 = []() -> uint64_t {
    auto [n, g] =
        make_transform([](uint64_t x) { return x * UINT64_C(2); }, UINT64_C(5));
    return n + g(UINT64_C(3));
  }();
  /// test2: make_transform(S, 10) = (11, go).
  /// go(5) = S(10) + 5 = 16. Total = 11 + 16 = 27.
  static inline const uint64_t test2 = []() -> uint64_t {
    auto [n, g] =
        make_transform([](uint64_t x) { return (x + 1); }, UINT64_C(10));
    return n + g(UINT64_C(5));
  }();
};
