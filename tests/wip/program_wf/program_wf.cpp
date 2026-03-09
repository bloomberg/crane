#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_wf.h>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int>
ProgramWf::jump_target(const std::shared_ptr<ProgramWf::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename ProgramWf::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ProgramWf::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ProgramWf::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
