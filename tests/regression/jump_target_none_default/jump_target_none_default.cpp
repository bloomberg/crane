#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jump_target_none_default.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> JumpTargetNoneDefault::jump_target(
    const std::shared_ptr<JumpTargetNoneDefault::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename JumpTargetNoneDefault::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename JumpTargetNoneDefault::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename JumpTargetNoneDefault::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
