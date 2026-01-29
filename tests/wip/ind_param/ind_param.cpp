#include <algorithm>
#include <any>
#include <functional>
#include <ind_param.h>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

unsigned int NatContainer::size(const std::shared_ptr<NatContainer::t> &c) {
  return std::visit(
      Overloaded{
          [](const typename NatContainer::t::Empty _args) -> unsigned int {
            return 0;
          },
          [](const typename NatContainer::t::Single _args) -> unsigned int {
            return (0 + 1);
          },
          [](const typename NatContainer::t::Pair _args) -> unsigned int {
            return ((0 + 1) + 1);
          }},
      c->v());
}
