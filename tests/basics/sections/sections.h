#ifndef INCLUDED_SECTIONS
#define INCLUDED_SECTIONS

#include <cstdint>

struct Sections {
  static uint64_t add_n(uint64_t x0_, uint64_t x1_);
  static uint64_t mul_n(uint64_t x0_, uint64_t x1_);
  static uint64_t add_five(uint64_t x0_);
  static uint64_t mul_three(uint64_t x0_);
  static uint64_t sum_ab(uint64_t x0_, uint64_t x1_);
  static uint64_t prod_ab(uint64_t x0_, uint64_t x1_);
  static uint64_t use_inner(uint64_t a);
  static constexpr uint64_t final_use = UINT64_C(8);

  template <typename T1> static T1 identity(T1 x) { return x; }

  template <typename T1> static T1 const_(T1 x, const T1 &) { return x; }

  static constexpr uint64_t test_add = UINT64_C(7);
  static constexpr uint64_t test_mul = UINT64_C(12);
  static constexpr uint64_t test_nested = UINT64_C(8);
  static constexpr uint64_t test_id = UINT64_C(7);
  static constexpr uint64_t test_const = UINT64_C(3);
};

#endif // INCLUDED_SECTIONS
