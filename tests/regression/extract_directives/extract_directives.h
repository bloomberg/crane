#ifndef INCLUDED_EXTRACT_DIRECTIVES
#define INCLUDED_EXTRACT_DIRECTIVES

#include <stdexcept>

struct ExtractDirectives {
  static uint64_t offset(uint64_t base, uint64_t x);
  static uint64_t scale(uint64_t base, uint64_t x);
  static uint64_t transform(uint64_t base, uint64_t x);
  static uint64_t safe_pred(uint64_t n);
  static inline const uint64_t test_offset = offset(UINT64_C(10), UINT64_C(5));
  static inline const uint64_t test_scale = scale(UINT64_C(3), UINT64_C(4));
  static inline const uint64_t test_transform =
      transform(UINT64_C(2), UINT64_C(3));
  static inline const uint64_t test_safe_pred = safe_pred(UINT64_C(5));
  static uint64_t inner_add(uint64_t _x0, uint64_t _x1);
  static uint64_t inner_mul(uint64_t _x0, uint64_t _x1);
  static uint64_t outer_use(uint64_t a, uint64_t b);
  static inline const uint64_t test_inner = inner_add(UINT64_C(3), UINT64_C(7));
  static inline const uint64_t test_outer = outer_use(UINT64_C(4), UINT64_C(5));
};

#endif // INCLUDED_EXTRACT_DIRECTIVES
