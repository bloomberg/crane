#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_status_write_chain.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> RamStatusWriteChain::reg_status(
    const std::shared_ptr<RamStatusWriteChain::ram_reg> &r) {
  return r->reg_status;
}

std::shared_ptr<List<std::shared_ptr<RamStatusWriteChain::ram_reg>>>
RamStatusWriteChain::chip_regs(
    const std::shared_ptr<RamStatusWriteChain::ram_chip> &r) {
  return r->chip_regs;
}

std::shared_ptr<List<std::shared_ptr<RamStatusWriteChain::ram_chip>>>
RamStatusWriteChain::bank_chips(
    const std::shared_ptr<RamStatusWriteChain::ram_bank> &r) {
  return r->bank_chips;
}

std::shared_ptr<List<std::shared_ptr<RamStatusWriteChain::ram_bank>>>
RamStatusWriteChain::ram_sys(
    const std::shared_ptr<RamStatusWriteChain::state> &s) {
  return s->ram_sys;
}

unsigned int RamStatusWriteChain::cur_bank(
    const std::shared_ptr<RamStatusWriteChain::state> &s) {
  return s->cur_bank;
}

unsigned int RamStatusWriteChain::sel_chip(
    const std::shared_ptr<RamStatusWriteChain::state> &s) {
  return s->sel_chip;
}

unsigned int RamStatusWriteChain::sel_reg(
    const std::shared_ptr<RamStatusWriteChain::state> &s) {
  return s->sel_reg;
}

std::shared_ptr<RamStatusWriteChain::ram_bank> RamStatusWriteChain::get_bank(
    const std::shared_ptr<RamStatusWriteChain::state> &s,
    const unsigned int b) {
  return s->ram_sys->nth(
      b,
      std::make_shared<RamStatusWriteChain::ram_bank>(ram_bank{
          List<std::shared_ptr<RamStatusWriteChain::ram_chip>>::ctor::nil_()}));
}

std::shared_ptr<RamStatusWriteChain::ram_chip> RamStatusWriteChain::get_chip(
    const std::shared_ptr<RamStatusWriteChain::ram_bank> &bk,
    const unsigned int c) {
  return bk->bank_chips->nth(
      c,
      std::make_shared<RamStatusWriteChain::ram_chip>(ram_chip{
          List<std::shared_ptr<RamStatusWriteChain::ram_reg>>::ctor::nil_()}));
}

std::shared_ptr<RamStatusWriteChain::ram_reg> RamStatusWriteChain::get_reg(
    const std::shared_ptr<RamStatusWriteChain::ram_chip> &ch,
    const unsigned int r) {
  return ch->chip_regs->nth(r, std::make_shared<RamStatusWriteChain::ram_reg>(
                                   ram_reg{List<unsigned int>::ctor::nil_()}));
}

std::shared_ptr<RamStatusWriteChain::ram_reg>
RamStatusWriteChain::upd_status_in_reg(
    std::shared_ptr<RamStatusWriteChain::ram_reg> rg, const unsigned int i,
    const unsigned int v) {
  return std::make_shared<RamStatusWriteChain::ram_reg>(
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
          std::move(rg)->reg_status)});
}

std::shared_ptr<RamStatusWriteChain::ram_chip>
RamStatusWriteChain::upd_reg_in_chip(
    std::shared_ptr<RamStatusWriteChain::ram_chip> ch, const unsigned int r,
    std::shared_ptr<RamStatusWriteChain::ram_reg> rg) {
  return std::make_shared<RamStatusWriteChain::ram_chip>(
      ram_chip{update_nth<std::shared_ptr<RamStatusWriteChain::ram_reg>>(
          std::move(r), std::move(rg), std::move(ch)->chip_regs)});
}

std::shared_ptr<RamStatusWriteChain::ram_bank>
RamStatusWriteChain::upd_chip_in_bank(
    std::shared_ptr<RamStatusWriteChain::ram_bank> bk, const unsigned int c,
    std::shared_ptr<RamStatusWriteChain::ram_chip> ch) {
  return std::make_shared<RamStatusWriteChain::ram_bank>(
      ram_bank{update_nth<std::shared_ptr<RamStatusWriteChain::ram_chip>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips)});
}

std::shared_ptr<List<std::shared_ptr<RamStatusWriteChain::ram_bank>>>
RamStatusWriteChain::upd_bank_in_sys(
    const std::shared_ptr<RamStatusWriteChain::state> &s, const unsigned int b,
    const std::shared_ptr<RamStatusWriteChain::ram_bank> &bk) {
  return update_nth<std::shared_ptr<RamStatusWriteChain::ram_bank>>(b, bk,
                                                                    s->ram_sys);
}

std::shared_ptr<List<std::shared_ptr<RamStatusWriteChain::ram_bank>>>
RamStatusWriteChain::ram_write_status_sys(
    const std::shared_ptr<RamStatusWriteChain::state> &s,
    const unsigned int idx, const unsigned int v) {
  unsigned int b = s->cur_bank;
  unsigned int c = s->sel_chip;
  unsigned int r = s->sel_reg;
  std::shared_ptr<RamStatusWriteChain::ram_bank> bk = get_bank(s, std::move(b));
  std::shared_ptr<RamStatusWriteChain::ram_chip> ch =
      get_chip(std::move(bk), std::move(c));
  std::shared_ptr<RamStatusWriteChain::ram_reg> rg =
      get_reg(std::move(ch), std::move(r));
  std::shared_ptr<RamStatusWriteChain::ram_reg> rg_ =
      upd_status_in_reg(std::move(rg), idx, v);
  std::shared_ptr<RamStatusWriteChain::ram_chip> ch_ =
      upd_reg_in_chip(std::move(ch), std::move(r), std::move(rg_));
  std::shared_ptr<RamStatusWriteChain::ram_bank> bk_ =
      upd_chip_in_bank(std::move(bk), std::move(c), std::move(ch_));
  return upd_bank_in_sys(s, std::move(b), std::move(bk_));
}
