#ifndef INCLUDED_PAGE_ADDRESS
#define INCLUDED_PAGE_ADDRESS

#include <utility>

struct PageAddress {
  static uint64_t addr12_of_nat(uint64_t n);
  static uint64_t page_of(uint64_t p);
  static uint64_t page_base(uint64_t p);
  static uint64_t branch_target(uint64_t pc, uint64_t off);
  static inline const uint64_t p_small = UINT64_C(777);
  static inline const uint64_t p_same = UINT64_C(600);
  static inline const uint64_t p_cross_254 = UINT64_C(254);
  static inline const uint64_t p_cross_255 = UINT64_C(255);
  static inline const uint64_t page_base_777 = page_base(UINT64_C(777));
  static inline const uint64_t branch_example =
      branch_target(UINT64_C(100), UINT64_C(42));
};

#endif // INCLUDED_PAGE_ADDRESS
