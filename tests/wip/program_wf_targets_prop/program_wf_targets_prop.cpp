#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_wf_targets_prop.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ProgramWfTargetsProp::base_addr(
    const std::shared_ptr<ProgramWfTargetsProp::layout> &l) {
  return l->base_addr;
}

unsigned int ProgramWfTargetsProp::code_size(
    const std::shared_ptr<ProgramWfTargetsProp::layout> &l) {
  return l->code_size;
}

std::optional<unsigned int> ProgramWfTargetsProp::jump_target(
    const std::shared_ptr<ProgramWfTargetsProp::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename ProgramWfTargetsProp::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ProgramWfTargetsProp::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ProgramWfTargetsProp::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
