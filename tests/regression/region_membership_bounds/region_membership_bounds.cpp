#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <region_membership_bounds.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int RegionMembershipBounds::base_addr(
    const std::shared_ptr<RegionMembershipBounds::layout> &l) {
  return l->base_addr;
}

unsigned int RegionMembershipBounds::code_size(
    const std::shared_ptr<RegionMembershipBounds::layout> &l) {
  return l->code_size;
}

bool RegionMembershipBounds::addr_in_regionb(
    const unsigned int addr,
    const std::shared_ptr<RegionMembershipBounds::layout> &l) {
  return ((l->base_addr <= addr) && (addr < (l->base_addr + l->code_size)));
}
