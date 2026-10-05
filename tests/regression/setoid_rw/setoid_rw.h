#ifndef INCLUDED_SETOID_RW
#define INCLUDED_SETOID_RW

#include <cstdint>
#include <utility>

struct SetoidRw {
  static uint64_t mod3(uint64_t n);
  static uint64_t classify_mod3(uint64_t n);
  static uint64_t add_mod3(uint64_t x, uint64_t y);
  static constexpr uint64_t test_mod3_0 = UINT64_C(0);
  static constexpr uint64_t test_mod3_5 = UINT64_C(2);
  static constexpr uint64_t test_mod3_9 = UINT64_C(0);
  static constexpr uint64_t test_classify_6 = UINT64_C(0);
  static constexpr uint64_t test_classify_7 = UINT64_C(1);
  static constexpr uint64_t test_add_mod3 = UINT64_C(0);
};

#endif // INCLUDED_SETOID_RW
