#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_specification_behavior_0040.h>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> ResetSpecificationBehavior0040::jump_target(
    const std::shared_ptr<ResetSpecificationBehavior0040::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename ResetSpecificationBehavior0040::instruction::JUN
                 _args) -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename ResetSpecificationBehavior0040::instruction::JMS
                 _args) -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename ResetSpecificationBehavior0040::instruction::NOP
                 _args) -> std::optional<unsigned int> {
            return std::nullopt;
          }},
      i->v());
}
