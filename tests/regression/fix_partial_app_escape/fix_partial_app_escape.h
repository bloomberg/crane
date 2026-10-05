#ifndef INCLUDED_FIX_PARTIAL_APP_ESCAPE
#define INCLUDED_FIX_PARTIAL_APP_ESCAPE

#include <cstdint>
#include <utility>

struct FixPartialAppEscape {
  static uint64_t count_bits(uint64_t x0_);
  static constexpr uint64_t test_0 = UINT64_C(0);
  static constexpr uint64_t test_1 = UINT64_C(1);
  static constexpr uint64_t test_7 = UINT64_C(3);
  static constexpr uint64_t test_255 = UINT64_C(8);
};

#endif // INCLUDED_FIX_PARTIAL_APP_ESCAPE
