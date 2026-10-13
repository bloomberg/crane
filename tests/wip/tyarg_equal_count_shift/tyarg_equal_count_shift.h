#ifndef INCLUDED_TYARG_EQUAL_COUNT_SHIFT
#define INCLUDED_TYARG_EQUAL_COUNT_SHIFT

#include <cstdint>

struct TyargEqualCountShift {
  template <typename T1, typename T2> static T2 pick_second(const T1 &, T2 b) {
    return b;
  }

  template <typename T1> static T1 partial_pick(uint64_t x0_, const T1 &x1_) {
    return pick_second<uint64_t, T1>(x0_, x1_);
  }

  static inline const bool chosen = partial_pick<bool>(UINT64_C(3), true);
  static inline const uint64_t chosen_nat =
      partial_pick<uint64_t>(UINT64_C(3), UINT64_C(9));

  static inline const bool full_pick =
      pick_second<uint64_t, bool>(UINT64_C(3), false);
};

#endif // INCLUDED_TYARG_EQUAL_COUNT_SHIFT
