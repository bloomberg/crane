#include <ind_param.h>

#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int IndParam::NatContainer::size(
    const std::shared_ptr<IndParam::NatContainer::t> &c) {
  if (std::holds_alternative<typename IndParam::NatContainer::t::Empty>(
          c->v())) {
    return 0u;
  } else if (std::holds_alternative<typename IndParam::NatContainer::t::Single>(
                 c->v())) {
    return 1u;
  } else {
    return 2u;
  }
}
