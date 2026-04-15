#include <program_wf_prop.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int> ProgramWfProp::jump_target(
    const std::shared_ptr<ProgramWfProp::instruction> &i) {
  if (std::holds_alternative<typename ProgramWfProp::instruction::JUN>(
          i->v())) {
    const auto &_m =
        *std::get_if<typename ProgramWfProp::instruction::JUN>(&i->v());
    return std::make_optional<unsigned int>(_m.d_a0);
  } else if (std::holds_alternative<typename ProgramWfProp::instruction::JMS>(
                 i->v())) {
    const auto &_m =
        *std::get_if<typename ProgramWfProp::instruction::JMS>(&i->v());
    return std::make_optional<unsigned int>(_m.d_a0);
  } else {
    return std::optional<unsigned int>();
  }
}
