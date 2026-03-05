#include <algorithm>
#include <any>
#include <cassert>
#include <decode_opcode_5_wf_behavior_0048.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> DecodeOpcode5WfBehavior0048::reg_main(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_reg> &r) {
  return r->reg_main;
}

std::shared_ptr<List<unsigned int>> DecodeOpcode5WfBehavior0048::reg_status(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_reg> &r) {
  return r->reg_status;
}

std::shared_ptr<List<std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_reg>>>
DecodeOpcode5WfBehavior0048::chip_regs(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_chip> &r) {
  return r->chip_regs;
}

unsigned int DecodeOpcode5WfBehavior0048::chip_port(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_chip> &r) {
  return r->chip_port;
}

std::shared_ptr<List<std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_chip>>>
DecodeOpcode5WfBehavior0048::bank_chips(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_bank> &r) {
  return r->bank_chips;
}

unsigned int DecodeOpcode5WfBehavior0048::sel_chip(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_sel> &r) {
  return r->sel_chip;
}

unsigned int DecodeOpcode5WfBehavior0048::sel_reg(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_sel> &r) {
  return r->sel_reg;
}

unsigned int DecodeOpcode5WfBehavior0048::sel_char(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_sel> &r) {
  return r->sel_char;
}

std::shared_ptr<List<std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_bank>>>
DecodeOpcode5WfBehavior0048::ram_sys(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::state> &s) {
  return s->ram_sys;
}

unsigned int DecodeOpcode5WfBehavior0048::cur_bank(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::state> &s) {
  return s->cur_bank;
}

std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_sel>
DecodeOpcode5WfBehavior0048::sel_ram(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::state> &s) {
  return s->sel_ram;
}

std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_bank>
DecodeOpcode5WfBehavior0048::get_bank(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::state> &s,
    const unsigned int b) {
  return s->ram_sys->nth(b, empty_bank);
}

std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_chip>
DecodeOpcode5WfBehavior0048::get_chip(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_bank> &bk,
    const unsigned int c) {
  return bk->bank_chips->nth(c, empty_chip);
}

std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_reg>
DecodeOpcode5WfBehavior0048::get_regRAM(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_chip> &ch,
    const unsigned int r) {
  return ch->chip_regs->nth(r, empty_reg);
}

unsigned int DecodeOpcode5WfBehavior0048::get_main(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_reg> &rg,
    const unsigned int i) {
  return rg->reg_main->nth(i, 0);
}

unsigned int DecodeOpcode5WfBehavior0048::ram_read_main(
    const std::shared_ptr<DecodeOpcode5WfBehavior0048::state> &s) {
  std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_bank> bk =
      get_bank(s, s->cur_bank);
  std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_chip> ch =
      get_chip(std::move(bk), s->sel_ram->sel_chip);
  std::shared_ptr<DecodeOpcode5WfBehavior0048::ram_reg> rg =
      get_regRAM(std::move(ch), s->sel_ram->sel_reg);
  return get_main(std::move(rg), s->sel_ram->sel_char);
}
