#include "program_wf.h"

std::optional<uint64_t>
ProgramWf::jump_target(const ProgramWf::instruction &i) {
  if (std::holds_alternative<typename ProgramWf::instruction::JUN>(i.v())) {
    const auto &[a0] = std::get<typename ProgramWf::instruction::JUN>(i.v());
    return std::make_optional<uint64_t>(a0);
  } else if (std::holds_alternative<typename ProgramWf::instruction::JMS>(
                 i.v())) {
    const auto &[a0] = std::get<typename ProgramWf::instruction::JMS>(i.v());
    return std::make_optional<uint64_t>(a0);
  } else {
    return std::optional<uint64_t>();
  }
}
