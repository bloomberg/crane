#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <ind_param.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int IndParam::NatContainer::size(const std::shared_ptr<t> &c) {
  return std::visit(
      Overloaded{
          [](const typename t::Empty _args) -> unsigned int { return 0; },
          [](const typename t::Single _args) -> unsigned int {
            return (0 + 1);
          },
          [](const typename t::Pair _args) -> unsigned int {
            return ((0 + 1) + 1);
          }},
      c->v());
}
