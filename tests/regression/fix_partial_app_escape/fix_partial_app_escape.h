#ifndef INCLUDED_FIX_PARTIAL_APP_ESCAPE
#define INCLUDED_FIX_PARTIAL_APP_ESCAPE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

struct FixPartialAppEscape {
  static unsigned int count_bits(const unsigned int _x0);
  static inline const unsigned int test_0 = count_bits(0u);
  static inline const unsigned int test_1 = count_bits(1u);
  static inline const unsigned int test_7 = count_bits(7u);
  static inline const unsigned int test_255 = count_bits(255u);
};

#endif // INCLUDED_FIX_PARTIAL_APP_ESCAPE
