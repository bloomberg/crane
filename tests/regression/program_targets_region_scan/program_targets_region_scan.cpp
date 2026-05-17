#include "program_targets_region_scan.h"

std::optional<uint64_t> ProgramTargetsRegionScan::jump_target(
    const ProgramTargetsRegionScan::instruction &i) {
  if (std::holds_alternative<
          typename ProgramTargetsRegionScan::instruction::JUN>(i.v())) {
    const auto &[a0] =
        std::get<typename ProgramTargetsRegionScan::instruction::JUN>(i.v());
    return std::make_optional<uint64_t>(a0);
  } else if (std::holds_alternative<
                 typename ProgramTargetsRegionScan::instruction::JMS>(i.v())) {
    const auto &[a0] =
        std::get<typename ProgramTargetsRegionScan::instruction::JMS>(i.v());
    return std::make_optional<uint64_t>(a0);
  } else {
    return std::optional<uint64_t>();
  }
}

bool ProgramTargetsRegionScan::addr_in_regionb(
    uint64_t addr, const ProgramTargetsRegionScan::layout &l) {
  return (l.base_addr <= addr && addr < (l.base_addr + l.code_size));
}

bool ProgramTargetsRegionScan::target_in_layoutb(
    const ProgramTargetsRegionScan::layout &l,
    const ProgramTargetsRegionScan::instruction &i) {
  auto _cs = jump_target(i);
  if (_cs.has_value()) {
    const uint64_t &a = *_cs;
    return addr_in_regionb(a, l);
  } else {
    return true;
  }
}

bool ProgramTargetsRegionScan::program_targets_okb(
    const List<ProgramTargetsRegionScan::instruction> &prog,
    const ProgramTargetsRegionScan::layout &l) {
  return prog.forallb(
      [=](ProgramTargetsRegionScan::instruction _x0) mutable -> bool {
        return target_in_layoutb(l, _x0);
      });
}
