#ifndef INCLUDED_EXTRACT_DIRECTIVES
#define INCLUDED_EXTRACT_DIRECTIVES

#include <cstdint>
#include <stdexcept>

struct ExtractDirectives {
  static uint64_t offset(uint64_t base, uint64_t x);
  static uint64_t scale(uint64_t base, uint64_t x);
  static uint64_t transform(uint64_t base, uint64_t x);
  static uint64_t safe_pred(uint64_t n);
  static constexpr uint64_t test_offset = UINT64_C(15);
  static constexpr uint64_t test_scale = UINT64_C(12);
  static constexpr uint64_t test_transform = UINT64_C(10);
  static constexpr uint64_t test_safe_pred = UINT64_C(4);
  static uint64_t inner_add(uint64_t x0_, uint64_t x1_);
  static uint64_t inner_mul(uint64_t x0_, uint64_t x1_);
  static uint64_t outer_use(uint64_t a, uint64_t b);
  static constexpr uint64_t test_inner = UINT64_C(10);
  static constexpr uint64_t test_outer = UINT64_C(29);
};

#endif // INCLUDED_EXTRACT_DIRECTIVES
