#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_6_behavior_0076.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> DecodeWfOpcode6Behavior0076::jump_target(
    const std::shared_ptr<DecodeWfOpcode6Behavior0076::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename DecodeWfOpcode6Behavior0076::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename DecodeWfOpcode6Behavior0076::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename DecodeWfOpcode6Behavior0076::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
