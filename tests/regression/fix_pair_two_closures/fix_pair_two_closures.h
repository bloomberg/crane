#ifndef INCLUDED_FIX_PAIR_TWO_CLOSURES
#define INCLUDED_FIX_PAIR_TWO_CLOSURES

#include "fn.h"
#include <cstdint>
#include <utility>

struct FixPairTwoClosures {
  /// Two local fixpoints escape through a pair.
  ///
  /// BUG: Both f and g use & capture. They capture a, b,
  /// and each other's std::function variables. All captured references
  /// dangle after make_ops returns.
  static std::pair<crane::fn<uint64_t(uint64_t)>, crane::fn<uint64_t(uint64_t)>>
  make_ops(uint64_t a, uint64_t b);
  /// test1: make_ops(10, 20). fst(3) = 10+3 = 13, snd(5) = 20+5 = 25.
  /// Total = 38.
  static constexpr uint64_t test1 = UINT64_C(38);
  /// test2: Use both closures interleaved.
  /// fst(1) + snd(2) + fst(3) = 11 + 22 + 13 = 46.
  static constexpr uint64_t test2 = UINT64_C(46);
  /// test3: Asymmetric arguments to stress different captured values.
  /// make_ops(100, 1). fst(0) + snd(0) = 100 + 1 = 101.
  static constexpr uint64_t test3 = UINT64_C(101);
};

#endif // INCLUDED_FIX_PAIR_TWO_CLOSURES
