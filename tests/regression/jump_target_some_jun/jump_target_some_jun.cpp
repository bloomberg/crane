#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jump_target_some_jun.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> JumpTargetSomeJun::jump_target(
    const std::shared_ptr<JumpTargetSomeJun::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename JumpTargetSomeJun::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargetSomeJun::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargetSomeJun::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

unsigned int
JumpTargetSomeJun::target_default(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int a = *o;
    return a;
  } else {
    return 0;
  }
}
