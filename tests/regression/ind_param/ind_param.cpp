#include <ind_param.h>

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

__attribute__((pure)) unsigned int IndParam::NatContainer::size(
    const std::shared_ptr<IndParam::NatContainer::t> &c) {
  return std::visit(
      Overloaded{[](const typename IndParam::NatContainer::t::Empty _args)
                     -> unsigned int { return 0u; },
                 [](const typename IndParam::NatContainer::t::Single _args)
                     -> unsigned int { return 1u; },
                 [](const typename IndParam::NatContainer::t::Pair _args)
                     -> unsigned int { return 2u; }},
      c->v());
}
