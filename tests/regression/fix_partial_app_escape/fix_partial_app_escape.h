#ifndef INCLUDED_FIX_PARTIAL_APP_ESCAPE
#define INCLUDED_FIX_PARTIAL_APP_ESCAPE

#include <utility>

struct FixPartialAppEscape {
  static uint64_t count_bits(uint64_t _x0);
  static inline const uint64_t test_0 = count_bits(UINT64_C(0));
  static inline const uint64_t test_1 = count_bits(UINT64_C(1));
  static inline const uint64_t test_7 = count_bits(UINT64_C(7));
  static inline const uint64_t test_255 = count_bits(UINT64_C(255));
};

#endif // INCLUDED_FIX_PARTIAL_APP_ESCAPE
