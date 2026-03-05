#include <algorithm>
#include <any>
#include <cassert>
#include <empty_bank_chip_count.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> EmptyBankChipCount::reg_main(
    const std::shared_ptr<EmptyBankChipCount::ram_reg> &r) {
  return r->reg_main;
}

std::shared_ptr<List<unsigned int>> EmptyBankChipCount::reg_status(
    const std::shared_ptr<EmptyBankChipCount::ram_reg> &r) {
  return r->reg_status;
}

std::shared_ptr<List<std::shared_ptr<EmptyBankChipCount::ram_reg>>>
EmptyBankChipCount::chip_regs(
    const std::shared_ptr<EmptyBankChipCount::ram_chip> &r) {
  return r->chip_regs;
}

unsigned int EmptyBankChipCount::chip_port(
    const std::shared_ptr<EmptyBankChipCount::ram_chip> &r) {
  return r->chip_port;
}

std::shared_ptr<List<std::shared_ptr<EmptyBankChipCount::ram_chip>>>
EmptyBankChipCount::bank_chips(
    const std::shared_ptr<EmptyBankChipCount::ram_bank> &r) {
  return r->bank_chips;
}
