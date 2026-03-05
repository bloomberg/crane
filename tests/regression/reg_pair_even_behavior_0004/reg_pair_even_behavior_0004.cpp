#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reg_pair_even_behavior_0004.h>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> RegPairEvenBehavior0004::jump_target(
    const std::shared_ptr<RegPairEvenBehavior0004::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename RegPairEvenBehavior0004::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename RegPairEvenBehavior0004::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename RegPairEvenBehavior0004::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
