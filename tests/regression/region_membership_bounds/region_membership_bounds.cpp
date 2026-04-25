#include <region_membership_bounds.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) bool RegionMembershipBounds::addr_in_regionb(
    const unsigned int &addr, const RegionMembershipBounds::layout &l) {
  return (l.base_addr <= addr && addr < (l.base_addr + l.code_size));
}
