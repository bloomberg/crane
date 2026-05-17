#ifndef INCLUDED_PAGE_ADDRESS
#define INCLUDED_PAGE_ADDRESS

#include <utility>

struct PageAddress {
  static unsigned int addr12_of_nat(unsigned int n);
  static unsigned int page_of(unsigned int p);
  static unsigned int page_base(unsigned int p);
  static unsigned int branch_target(unsigned int pc, unsigned int off);
  static inline const unsigned int p_small = 777u;
  static inline const unsigned int p_same = 600u;
  static inline const unsigned int p_cross_254 = 254u;
  static inline const unsigned int p_cross_255 = 255u;
  static inline const unsigned int page_base_777 = page_base(777u);
  static inline const unsigned int branch_example = branch_target(100u, 42u);
};

#endif // INCLUDED_PAGE_ADDRESS
