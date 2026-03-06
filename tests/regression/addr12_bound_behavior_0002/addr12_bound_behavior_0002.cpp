#include <addr12_bound_behavior_0002.h>
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

std::optional<unsigned int> Addr12BoundBehavior0002::jump_target(
    const std::shared_ptr<Addr12BoundBehavior0002::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename Addr12BoundBehavior0002::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename Addr12BoundBehavior0002::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename Addr12BoundBehavior0002::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

unsigned int
Addr12BoundBehavior0002::target_default(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int a = *o;
    return a;
  } else {
    return 0;
  }
}
