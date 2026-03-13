#include <program_wf_prop.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) std::optional<unsigned int> ProgramWfProp::jump_target(
    const std::shared_ptr<ProgramWfProp::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename ProgramWfProp::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ProgramWfProp::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args.d_a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename ProgramWfProp::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
