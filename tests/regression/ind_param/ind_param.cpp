#include <ind_param.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int IndParam::NatContainer::size(
    const std::shared_ptr<IndParam::NatContainer::t> &c) {
  return std::visit(
      Overloaded{
          [](const typename IndParam::NatContainer::t::Empty) -> unsigned int {
            return 0u;
          },
          [](const typename IndParam::NatContainer::t::Single) -> unsigned int {
            return 1u;
          },
          [](const typename IndParam::NatContainer::t::Pair) -> unsigned int {
            return 2u;
          }},
      c->v());
}
