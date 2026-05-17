#include "program_wf_prop.h"

std::optional<unsigned int>
ProgramWfProp::jump_target(const ProgramWfProp::instruction &i) {
  if (std::holds_alternative<typename ProgramWfProp::instruction::JUN>(i.v())) {
    const auto &[a0] =
        std::get<typename ProgramWfProp::instruction::JUN>(i.v());
    return std::make_optional<unsigned int>(a0);
  } else if (std::holds_alternative<typename ProgramWfProp::instruction::JMS>(
                 i.v())) {
    const auto &[a0] =
        std::get<typename ProgramWfProp::instruction::JMS>(i.v());
    return std::make_optional<unsigned int>(a0);
  } else {
    return std::optional<unsigned int>();
  }
}
