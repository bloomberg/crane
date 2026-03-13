#include <ram_write.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
RamWrite::get_main(const std::shared_ptr<RamWrite::ram_reg> &rg,
                   const unsigned int i) {
  return rg->reg_main->nth(i, 0u);
}

std::shared_ptr<RamWrite::ram_reg>
RamWrite::upd_main_in_reg(std::shared_ptr<RamWrite::ram_reg> rg,
                          const unsigned int i, const unsigned int v) {
  return std::make_shared<RamWrite::ram_reg>(
      ram_reg{update_nth<unsigned int>(std::move(i), (std::move(v) % 16u),
                                       rg->reg_main),
              rg->reg_status});
}

std::shared_ptr<RamWrite::ram_reg>
RamWrite::upd_stat_in_reg(std::shared_ptr<RamWrite::ram_reg> rg,
                          const unsigned int i, const unsigned int v) {
  return std::make_shared<RamWrite::ram_reg>(ram_reg{
      rg->reg_main, update_nth<unsigned int>(std::move(i), (std::move(v) % 16u),
                                             rg->reg_status)});
}

std::shared_ptr<RamWrite::ram_reg>
RamWrite::get_regRAM(const std::shared_ptr<RamWrite::ram_chip> &ch,
                     const unsigned int r) {
  return ch->chip_regs->nth(r, empty_reg);
}

std::shared_ptr<RamWrite::ram_chip>
RamWrite::upd_reg_in_chip(std::shared_ptr<RamWrite::ram_chip> ch,
                          const unsigned int r,
                          std::shared_ptr<RamWrite::ram_reg> rg) {
  return std::make_shared<RamWrite::ram_chip>(
      ram_chip{update_nth<std::shared_ptr<RamWrite::ram_reg>>(
                   std::move(r), std::move(rg), ch->chip_regs),
               ch->chip_port});
}

std::shared_ptr<RamWrite::ram_chip>
RamWrite::get_chip(const std::shared_ptr<RamWrite::ram_bank> &bk,
                   const unsigned int c) {
  return bk->bank_chips->nth(c, empty_chip);
}

std::shared_ptr<RamWrite::ram_bank>
RamWrite::upd_chip_in_bank(std::shared_ptr<RamWrite::ram_bank> bk,
                           const unsigned int c,
                           std::shared_ptr<RamWrite::ram_chip> ch) {
  return std::make_shared<RamWrite::ram_bank>(
      ram_bank{update_nth<std::shared_ptr<RamWrite::ram_chip>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips)});
}

std::shared_ptr<RamWrite::ram_bank> RamWrite::get_bank_from_sys(
    const std::shared_ptr<List<std::shared_ptr<RamWrite::ram_bank>>> &sys,
    const unsigned int b) {
  return sys->nth(b, empty_bank);
}

std::shared_ptr<List<std::shared_ptr<RamWrite::ram_bank>>>
RamWrite::upd_bank_in_sys(const std::shared_ptr<RamWrite::state> &s,
                          const unsigned int b,
                          const std::shared_ptr<RamWrite::ram_bank> &bk) {
  return update_nth<std::shared_ptr<RamWrite::ram_bank>>(b, bk, s->state_ram);
}

std::shared_ptr<RamWrite::ram_bank>
RamWrite::current_bank(const std::shared_ptr<RamWrite::state> &s) {
  return get_bank_from_sys(s->state_ram, s->state_sel->sel_bank);
}

std::shared_ptr<RamWrite::ram_chip>
RamWrite::current_chip(const std::shared_ptr<RamWrite::state> &s) {
  return get_chip(current_bank(s), s->state_sel->sel_chip);
}

std::shared_ptr<RamWrite::ram_reg>
RamWrite::current_reg(const std::shared_ptr<RamWrite::state> &s) {
  return get_regRAM(current_chip(s), s->state_sel->sel_reg);
}

__attribute__((pure)) unsigned int
RamWrite::ram_read_main(const std::shared_ptr<RamWrite::state> &s) {
  return get_main(current_reg(s), s->state_sel->sel_char);
}

std::shared_ptr<List<std::shared_ptr<RamWrite::ram_bank>>>
RamWrite::ram_write_main_sys(const std::shared_ptr<RamWrite::state> &s,
                             const unsigned int v) {
  std::shared_ptr<RamWrite::ram_reg> rg = current_reg(s);
  std::shared_ptr<RamWrite::ram_chip> ch = current_chip(s);
  std::shared_ptr<RamWrite::ram_bank> bk = current_bank(s);
  std::shared_ptr<RamWrite::ram_reg> rg_ =
      upd_main_in_reg(std::move(rg), s->state_sel->sel_char, v);
  std::shared_ptr<RamWrite::ram_chip> ch_ =
      upd_reg_in_chip(std::move(ch), s->state_sel->sel_reg, std::move(rg_));
  std::shared_ptr<RamWrite::ram_bank> bk_ =
      upd_chip_in_bank(std::move(bk), s->state_sel->sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s->state_sel->sel_bank, std::move(bk_));
}

std::shared_ptr<List<std::shared_ptr<RamWrite::ram_bank>>>
RamWrite::ram_write_status_sys(const std::shared_ptr<RamWrite::state> &s,
                               const unsigned int idx, const unsigned int v) {
  std::shared_ptr<RamWrite::ram_reg> rg = current_reg(s);
  std::shared_ptr<RamWrite::ram_chip> ch = current_chip(s);
  std::shared_ptr<RamWrite::ram_bank> bk = current_bank(s);
  std::shared_ptr<RamWrite::ram_reg> rg_ =
      upd_stat_in_reg(std::move(rg), idx, v);
  std::shared_ptr<RamWrite::ram_chip> ch_ =
      upd_reg_in_chip(std::move(ch), s->state_sel->sel_reg, std::move(rg_));
  std::shared_ptr<RamWrite::ram_bank> bk_ =
      upd_chip_in_bank(std::move(bk), s->state_sel->sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s->state_sel->sel_bank, std::move(bk_));
}
