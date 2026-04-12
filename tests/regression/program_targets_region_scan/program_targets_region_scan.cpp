#include <program_targets_region_scan.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) std::optional<unsigned int>
ProgramTargetsRegionScan::jump_target(
    const std::shared_ptr<ProgramTargetsRegionScan::instruction> &i) {
  return std::visit(
      Overloaded{
          [](const typename ProgramTargetsRegionScan::instruction::JUN _args)
              -> std::optional<unsigned int> {
            return std::make_optional<unsigned int>(_args.d_a0);
          },
          [](const typename ProgramTargetsRegionScan::instruction::JMS _args)
              -> std::optional<unsigned int> {
            return std::make_optional<unsigned int>(_args.d_a0);
          },
          [](const typename ProgramTargetsRegionScan::instruction::NOP)
              -> std::optional<unsigned int> {
            return std::optional<unsigned int>();
          }},
      i->v());
}

__attribute__((pure)) bool ProgramTargetsRegionScan::addr_in_regionb(
    const unsigned int addr,
    const std::shared_ptr<ProgramTargetsRegionScan::layout> &l) {
  return (l->base_addr <= addr && addr < (l->base_addr + l->code_size));
}

__attribute__((pure)) bool ProgramTargetsRegionScan::target_in_layoutb(
    const std::shared_ptr<ProgramTargetsRegionScan::layout> &l,
    const std::shared_ptr<ProgramTargetsRegionScan::instruction> &i) {
  auto _cs = jump_target(i);
  if (_cs.has_value()) {
    unsigned int a = *_cs;
    return addr_in_regionb(a, l);
  } else {
    return true;
  }
}

__attribute__((pure)) bool ProgramTargetsRegionScan::program_targets_okb(
    const std::shared_ptr<
        List<std::shared_ptr<ProgramTargetsRegionScan::instruction>>> &prog,
    std::shared_ptr<ProgramTargetsRegionScan::layout> l) {
  return prog->forallb(
      [=](const std::shared_ptr<ProgramTargetsRegionScan::instruction>
              &_x0) mutable -> bool { return target_in_layoutb(l, _x0); });
}
