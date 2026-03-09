#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_targets_region_scan.h>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> ProgramTargetsRegionScan::jump_target(
    const std::shared_ptr<ProgramTargetsRegionScan::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename ProgramTargetsRegionScan::instruction::JUN _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename ProgramTargetsRegionScan::instruction::JMS _args)
              -> std::optional<unsigned int> {
            unsigned int a = _args._a0;
            return std::make_optional<unsigned int>(std::move(a));
          },
          [](const typename ProgramTargetsRegionScan::instruction::NOP _args)
              -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}

bool ProgramTargetsRegionScan::addr_in_regionb(
    const unsigned int addr,
    const std::shared_ptr<ProgramTargetsRegionScan::layout> &l) {
  return ((l->base_addr <= addr) && (addr < (l->base_addr + l->code_size)));
}

bool ProgramTargetsRegionScan::target_in_layoutb(
    const std::shared_ptr<ProgramTargetsRegionScan::layout> &l,
    const std::shared_ptr<ProgramTargetsRegionScan::instruction> &i) {
  if (jump_target(i).has_value()) {
    unsigned int a = *jump_target(i);
    return addr_in_regionb(a, l);
  } else {
    return true;
  }
}

bool ProgramTargetsRegionScan::program_targets_okb(
    const std::shared_ptr<
        List<std::shared_ptr<ProgramTargetsRegionScan::instruction>>> &prog,
    const std::shared_ptr<ProgramTargetsRegionScan::layout> &l) {
  return prog->forallb(
      [&](const std::shared_ptr<ProgramTargetsRegionScan::instruction> _x0)
          -> bool { return target_in_layoutb(l, _x0); });
}
