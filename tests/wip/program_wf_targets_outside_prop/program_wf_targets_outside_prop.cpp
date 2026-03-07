#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_wf_targets_outside_prop.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ProgramWfTargetsOutsideProp::base_addr(
    const std::shared_ptr<ProgramWfTargetsOutsideProp::layout> &l) {
  return l->base_addr;
}

unsigned int ProgramWfTargetsOutsideProp::code_size(
    const std::shared_ptr<ProgramWfTargetsOutsideProp::layout> &l) {
  return l->code_size;
}

std::optional<unsigned int> ProgramWfTargetsOutsideProp::jump_target(
    const std::shared_ptr<ProgramWfTargetsOutsideProp::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename ProgramWfTargetsOutsideProp::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename ProgramWfTargetsOutsideProp::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename ProgramWfTargetsOutsideProp::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
