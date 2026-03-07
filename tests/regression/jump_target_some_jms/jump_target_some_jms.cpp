#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <jump_target_some_jms.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> JumpTargetSomeJms::jump_target(
    const std::shared_ptr<JumpTargetSomeJms::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename JumpTargetSomeJms::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargetSomeJms::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename JumpTargetSomeJms::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

unsigned int
JumpTargetSomeJms::option_nat_or_zero(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int n = *o;
    return n;
  } else {
    return 0;
  }
}
