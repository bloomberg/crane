#include <program_wf.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
ProgramWf::jump_target(const std::shared_ptr<ProgramWf::instruction> &i) {
  if (std::holds_alternative<typename ProgramWf::instruction::JUN>(i->v())) {
    const auto &_m =
        *std::get_if<typename ProgramWf::instruction::JUN>(&i->v());
    return std::make_optional<unsigned int>(_m.d_a0);
  } else if (std::holds_alternative<typename ProgramWf::instruction::JMS>(
                 i->v())) {
    const auto &_m =
        *std::get_if<typename ProgramWf::instruction::JMS>(&i->v());
    return std::make_optional<unsigned int>(_m.d_a0);
  } else {
    return std::optional<unsigned int>();
  }
}
