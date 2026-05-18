#ifndef INCLUDED_SETOID_RW
#define INCLUDED_SETOID_RW

#include <utility>

struct SetoidRw {
  static uint64_t mod3(uint64_t n);
  static uint64_t classify_mod3(uint64_t n);
  static uint64_t add_mod3(uint64_t x, uint64_t y);
  static inline const uint64_t test_mod3_0 = mod3(UINT64_C(0));
  static inline const uint64_t test_mod3_5 = mod3(UINT64_C(5));
  static inline const uint64_t test_mod3_9 = mod3(UINT64_C(9));
  static inline const uint64_t test_classify_6 = classify_mod3(UINT64_C(6));
  static inline const uint64_t test_classify_7 = classify_mod3(UINT64_C(7));
  static inline const uint64_t test_add_mod3 =
      add_mod3(UINT64_C(5), UINT64_C(7));
};

#endif // INCLUDED_SETOID_RW
