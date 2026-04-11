#include <program_wf.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
ProgramWf::jump_target(const std::shared_ptr<ProgramWf::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename ProgramWf::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   return std::make_optional<unsigned int>(_args.d_a0);
                 },
                 [](const typename ProgramWf::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   return std::make_optional<unsigned int>(_args.d_a0);
                 },
                 [](const typename ProgramWf::instruction::NOP)
                     -> std::optional<unsigned int> {
                   return std::optional<unsigned int>();
                 }},
      i->v());
}
