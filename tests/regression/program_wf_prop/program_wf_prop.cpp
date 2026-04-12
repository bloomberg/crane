#include <program_wf_prop.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int> ProgramWfProp::jump_target(
    const std::shared_ptr<ProgramWfProp::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename ProgramWfProp::instruction::JUN &_args)
                     -> std::optional<unsigned int> {
                   return std::make_optional<unsigned int>(_args.d_a0);
                 },
                 [](const typename ProgramWfProp::instruction::JMS &_args)
                     -> std::optional<unsigned int> {
                   return std::make_optional<unsigned int>(_args.d_a0);
                 },
                 [](const typename ProgramWfProp::instruction::NOP &)
                     -> std::optional<unsigned int> {
                   return std::optional<unsigned int>();
                 }},
      i->v());
}
