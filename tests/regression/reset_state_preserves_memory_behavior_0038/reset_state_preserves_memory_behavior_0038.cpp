#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_state_preserves_memory_behavior_0038.h>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> ResetStatePreservesMemoryBehavior0038::jump_target(
    const std::shared_ptr<ResetStatePreservesMemoryBehavior0038::instruction>
        &i) {
  return std::visit(
      Overloaded{[](const typename ResetStatePreservesMemoryBehavior0038::
                        instruction::JUN _args) -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ResetStatePreservesMemoryBehavior0038::
                        instruction::JMS _args) -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ResetStatePreservesMemoryBehavior0038::
                        instruction::NOP _args) -> std::optional<unsigned int> {
                   return std::nullopt;
                 }},
      i->v());
}

unsigned int ResetStatePreservesMemoryBehavior0038::target_default(
    const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int a = *o;
    return a;
  } else {
    return 0;
  }
}
