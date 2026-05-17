#ifndef INCLUDED_REGION_MEMBERSHIP_BOUNDS
#define INCLUDED_REGION_MEMBERSHIP_BOUNDS

struct RegionMembershipBounds {
  struct layout {
    unsigned int base_addr;
    unsigned int code_size;

    // ACCESSORS
    layout clone() const {
      return layout{(*this).base_addr, (*this).code_size};
    }
  };

  static bool addr_in_regionb(unsigned int addr, const layout &l);
  static inline const unsigned int t = []() {
    return []() {
      layout l = layout{100u, 20u};
      return ((addr_in_regionb(110u, l) ? 1u : 0u) +
              (addr_in_regionb(121u, l) ? 1u : 0u));
    }();
  }();
};

#endif // INCLUDED_REGION_MEMBERSHIP_BOUNDS
