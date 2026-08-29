#include "ind_param.h"

uint64_t IndParam::NatContainer::size(const IndParam::NatContainer::t &c) {
  if (std::holds_alternative<typename IndParam::NatContainer::t::Empty>(
          c.v())) {
    return UINT64_C(0);
  } else if (std::holds_alternative<typename IndParam::NatContainer::t::Single>(
                 c.v())) {
    return UINT64_C(1);
  } else {
    return UINT64_C(2);
  }
}
