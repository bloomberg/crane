#include <ind_param.h>

__attribute__((pure)) unsigned int
IndParam::NatContainer::size(const IndParam::NatContainer::t &c) {
  if (std::holds_alternative<typename IndParam::NatContainer::t::Empty>(
          c.v())) {
    return 0u;
  } else if (std::holds_alternative<typename IndParam::NatContainer::t::Single>(
                 c.v())) {
    return 1u;
  } else {
    return 2u;
  }
}
