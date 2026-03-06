#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_main_write_chain.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> RamMainWriteChain::reg_main(
    const std::shared_ptr<RamMainWriteChain::ram_reg> &r) {
  return r->reg_main;
}

std::shared_ptr<List<std::shared_ptr<RamMainWriteChain::ram_reg>>>
RamMainWriteChain::chip_regs(
    const std::shared_ptr<RamMainWriteChain::ram_chip> &r) {
  return r->chip_regs;
}

std::shared_ptr<List<std::shared_ptr<RamMainWriteChain::ram_chip>>>
RamMainWriteChain::bank_chips(
    const std::shared_ptr<RamMainWriteChain::ram_bank> &r) {
  return r->bank_chips;
}

std::shared_ptr<List<std::shared_ptr<RamMainWriteChain::ram_bank>>>
RamMainWriteChain::ram_sys(const std::shared_ptr<RamMainWriteChain::state> &s) {
  return s->ram_sys;
}

unsigned int RamMainWriteChain::cur_bank(
    const std::shared_ptr<RamMainWriteChain::state> &s) {
  return s->cur_bank;
}

unsigned int RamMainWriteChain::sel_chip(
    const std::shared_ptr<RamMainWriteChain::state> &s) {
  return s->sel_chip;
}

unsigned int
RamMainWriteChain::sel_reg(const std::shared_ptr<RamMainWriteChain::state> &s) {
  return s->sel_reg;
}

unsigned int RamMainWriteChain::sel_char(
    const std::shared_ptr<RamMainWriteChain::state> &s) {
  return s->sel_char;
}

std::shared_ptr<RamMainWriteChain::ram_bank>
RamMainWriteChain::get_bank(const std::shared_ptr<RamMainWriteChain::state> &s,
                            const unsigned int b) {
  return s->ram_sys->nth(
      b,
      std::make_shared<RamMainWriteChain::ram_bank>(ram_bank{
          List<std::shared_ptr<RamMainWriteChain::ram_chip>>::ctor::nil_()}));
}

std::shared_ptr<RamMainWriteChain::ram_chip> RamMainWriteChain::get_chip(
    const std::shared_ptr<RamMainWriteChain::ram_bank> &bk,
    const unsigned int c) {
  return bk->bank_chips->nth(
      c, std::make_shared<RamMainWriteChain::ram_chip>(ram_chip{
             List<std::shared_ptr<RamMainWriteChain::ram_reg>>::ctor::nil_()}));
}

std::shared_ptr<RamMainWriteChain::ram_reg> RamMainWriteChain::get_reg(
    const std::shared_ptr<RamMainWriteChain::ram_chip> &ch,
    const unsigned int r) {
  return ch->chip_regs->nth(r, std::make_shared<RamMainWriteChain::ram_reg>(
                                   ram_reg{List<unsigned int>::ctor::nil_()}));
}

std::shared_ptr<RamMainWriteChain::ram_reg> RamMainWriteChain::upd_main_in_reg(
    std::shared_ptr<RamMainWriteChain::ram_reg> rg, const unsigned int i,
    const unsigned int v) {
  return std::make_shared<RamMainWriteChain::ram_reg>(
      ram_reg{update_nth<unsigned int>(
          std::move(i),
          (std::move(v) %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          std::move(rg)->reg_main)});
}

std::shared_ptr<RamMainWriteChain::ram_chip> RamMainWriteChain::upd_reg_in_chip(
    std::shared_ptr<RamMainWriteChain::ram_chip> ch, const unsigned int r,
    std::shared_ptr<RamMainWriteChain::ram_reg> rg) {
  return std::make_shared<RamMainWriteChain::ram_chip>(
      ram_chip{update_nth<std::shared_ptr<RamMainWriteChain::ram_reg>>(
          std::move(r), std::move(rg), std::move(ch)->chip_regs)});
}

std::shared_ptr<RamMainWriteChain::ram_bank>
RamMainWriteChain::upd_chip_in_bank(
    std::shared_ptr<RamMainWriteChain::ram_bank> bk, const unsigned int c,
    std::shared_ptr<RamMainWriteChain::ram_chip> ch) {
  return std::make_shared<RamMainWriteChain::ram_bank>(
      ram_bank{update_nth<std::shared_ptr<RamMainWriteChain::ram_chip>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips)});
}

std::shared_ptr<List<std::shared_ptr<RamMainWriteChain::ram_bank>>>
RamMainWriteChain::upd_bank_in_sys(
    const std::shared_ptr<RamMainWriteChain::state> &s, const unsigned int b,
    const std::shared_ptr<RamMainWriteChain::ram_bank> &bk) {
  return update_nth<std::shared_ptr<RamMainWriteChain::ram_bank>>(b, bk,
                                                                  s->ram_sys);
}

std::shared_ptr<List<std::shared_ptr<RamMainWriteChain::ram_bank>>>
RamMainWriteChain::ram_write_main_sys(
    const std::shared_ptr<RamMainWriteChain::state> &s, const unsigned int v) {
  unsigned int b = s->cur_bank;
  unsigned int c = s->sel_chip;
  unsigned int r = s->sel_reg;
  unsigned int i = s->sel_char;
  std::shared_ptr<RamMainWriteChain::ram_bank> bk = get_bank(s, std::move(b));
  std::shared_ptr<RamMainWriteChain::ram_chip> ch =
      get_chip(std::move(bk), std::move(c));
  std::shared_ptr<RamMainWriteChain::ram_reg> rg =
      get_reg(std::move(ch), std::move(r));
  std::shared_ptr<RamMainWriteChain::ram_reg> rg_ =
      upd_main_in_reg(std::move(rg), std::move(i), v);
  std::shared_ptr<RamMainWriteChain::ram_chip> ch_ =
      upd_reg_in_chip(std::move(ch), std::move(r), std::move(rg_));
  std::shared_ptr<RamMainWriteChain::ram_bank> bk_ =
      upd_chip_in_bank(std::move(bk), std::move(c), std::move(ch_));
  return upd_bank_in_sys(s, std::move(b), std::move(bk_));
}
