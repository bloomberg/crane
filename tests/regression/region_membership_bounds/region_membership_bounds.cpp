#include <region_membership_bounds.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) bool RegionMembershipBounds::addr_in_regionb(
    const unsigned int addr,
    const std::shared_ptr<RegionMembershipBounds::layout> &l) {
  return (l->base_addr <= addr && addr < (l->base_addr + l->code_size));
}
