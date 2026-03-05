#include <algorithm>
#include <any>
#include <cassert>
#include <empty_chip_register_count.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> EmptyChipRegisterCount::reg_main(
    const std::shared_ptr<EmptyChipRegisterCount::ram_reg> &r) {
  return r->reg_main;
}

std::shared_ptr<List<unsigned int>> EmptyChipRegisterCount::reg_status(
    const std::shared_ptr<EmptyChipRegisterCount::ram_reg> &r) {
  return r->reg_status;
}

std::shared_ptr<List<std::shared_ptr<EmptyChipRegisterCount::ram_reg>>>
EmptyChipRegisterCount::chip_regs(
    const std::shared_ptr<EmptyChipRegisterCount::ram_chip> &r) {
  return r->chip_regs;
}

unsigned int EmptyChipRegisterCount::chip_port(
    const std::shared_ptr<EmptyChipRegisterCount::ram_chip> &r) {
  return r->chip_port;
}
