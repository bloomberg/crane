#include <program_targets_region_scan.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
ProgramTargetsRegionScan::jump_target(
    const ProgramTargetsRegionScan::instruction &i) {
  if (std::holds_alternative<
          typename ProgramTargetsRegionScan::instruction::JUN>(i.v())) {
    const auto &[d_a0] =
        std::get<typename ProgramTargetsRegionScan::instruction::JUN>(i.v());
    return std::make_optional<unsigned int>(d_a0);
  } else if (std::holds_alternative<
                 typename ProgramTargetsRegionScan::instruction::JMS>(i.v())) {
    const auto &[d_a0] =
        std::get<typename ProgramTargetsRegionScan::instruction::JMS>(i.v());
    return std::make_optional<unsigned int>(d_a0);
  } else {
    return std::optional<unsigned int>();
  }
}

__attribute__((pure)) bool ProgramTargetsRegionScan::addr_in_regionb(
    const unsigned int &addr, const ProgramTargetsRegionScan::layout &l) {
  return (l.base_addr <= addr && addr < (l.base_addr + l.code_size));
}

__attribute__((pure)) bool ProgramTargetsRegionScan::target_in_layoutb(
    const ProgramTargetsRegionScan::layout &l,
    const ProgramTargetsRegionScan::instruction &i) {
  auto _cs = jump_target(i);
  if (_cs.has_value()) {
    const unsigned int &a = *_cs;
    return addr_in_regionb(a, l);
  } else {
    return true;
  }
}

__attribute__((pure)) bool ProgramTargetsRegionScan::program_targets_okb(
    const List<ProgramTargetsRegionScan::instruction> &prog,
    ProgramTargetsRegionScan::layout l) {
  return prog.forallb(
      [=](ProgramTargetsRegionScan::instruction _x0) mutable -> bool {
        return target_in_layoutb(l, _x0);
      });
}
