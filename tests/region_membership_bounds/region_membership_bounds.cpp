#include "region_membership_bounds.h"

bool RegionMembershipBounds::addr_in_regionb(
    uint64_t addr, const RegionMembershipBounds::layout &l) {
  return (l.base_addr <= addr && addr < (l.base_addr + l.code_size));
}
