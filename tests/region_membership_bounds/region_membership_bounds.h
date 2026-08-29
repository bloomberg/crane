#ifndef INCLUDED_REGION_MEMBERSHIP_BOUNDS
#define INCLUDED_REGION_MEMBERSHIP_BOUNDS

#include <utility>

struct RegionMembershipBounds {
  struct layout {
    uint64_t base_addr;
    uint64_t code_size;
  };

  static bool addr_in_regionb(uint64_t addr, const layout &l);
  static inline const uint64_t t = []() {
    return []() {
      layout l = layout{UINT64_C(100), UINT64_C(20)};
      return ((addr_in_regionb(UINT64_C(110), std::move(l)) ? UINT64_C(1)
                                                            : UINT64_C(0)) +
              (addr_in_regionb(UINT64_C(121), std::move(l)) ? UINT64_C(1)
                                                            : UINT64_C(0)));
    }();
  }();
};

#endif // INCLUDED_REGION_MEMBERSHIP_BOUNDS
