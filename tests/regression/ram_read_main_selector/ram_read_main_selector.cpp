#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_read_main_selector.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<RamReadMainSelector::ram_bank> RamReadMainSelector::get_bank(
    const std::shared_ptr<RamReadMainSelector::state> &s,
    const unsigned int b) {
  return s->ram_sys->nth(b, empty_bank);
}

std::shared_ptr<RamReadMainSelector::ram_chip> RamReadMainSelector::get_chip(
    const std::shared_ptr<RamReadMainSelector::ram_bank> &bk,
    const unsigned int c) {
  return bk->bank_chips->nth(c, empty_chip);
}

std::shared_ptr<RamReadMainSelector::ram_reg> RamReadMainSelector::get_regRAM(
    const std::shared_ptr<RamReadMainSelector::ram_chip> &ch,
    const unsigned int r) {
  return ch->chip_regs->nth(r, empty_reg);
}

unsigned int RamReadMainSelector::get_main(
    const std::shared_ptr<RamReadMainSelector::ram_reg> &rg,
    const unsigned int i) {
  return rg->reg_main->nth(i, 0u);
}

unsigned int RamReadMainSelector::ram_read_main(
    const std::shared_ptr<RamReadMainSelector::state> &s) {
  std::shared_ptr<RamReadMainSelector::ram_bank> bk = get_bank(s, s->cur_bank);
  std::shared_ptr<RamReadMainSelector::ram_chip> ch =
      get_chip(std::move(bk), s->sel_ram->sel_chip);
  std::shared_ptr<RamReadMainSelector::ram_reg> rg =
      get_regRAM(std::move(ch), s->sel_ram->sel_reg);
  return get_main(std::move(rg), s->sel_ram->sel_char);
}
