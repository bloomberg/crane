#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_4_behavior_0074.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> DecodeWfOpcode4Behavior0074::jump_target(
    const std::shared_ptr<DecodeWfOpcode4Behavior0074::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename DecodeWfOpcode4Behavior0074::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename DecodeWfOpcode4Behavior0074::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename DecodeWfOpcode4Behavior0074::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

unsigned int DecodeWfOpcode4Behavior0074::target_default(
    const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int a = *o;
    return a;
  } else {
    return 0;
  }
}
