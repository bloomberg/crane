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
#include <wf_chip_upd_reg_prop.h>

std::shared_ptr<WfChipUpdRegProp::state>
WfChipUpdRegProp::reset_state(std::shared_ptr<WfChipUpdRegProp::state> s) {
  return std::make_shared<WfChipUpdRegProp::state>(
      state{s->state_regs, 0, false, 0, List<unsigned int>::ctor::nil_(),
            s->state_ram, default_sel, s->state_rom});
}

unsigned int
WfChipUpdRegProp::get_main(const std::shared_ptr<WfChipUpdRegProp::ram_reg> &rg,
                           const unsigned int i) {
  return rg->reg_main->nth(i, 0);
}

unsigned int
WfChipUpdRegProp::get_stat(const std::shared_ptr<WfChipUpdRegProp::ram_reg> &rg,
                           const unsigned int i) {
  return rg->reg_status->nth(i, 0);
}

std::shared_ptr<WfChipUpdRegProp::ram_reg>
WfChipUpdRegProp::upd_main_in_reg(std::shared_ptr<WfChipUpdRegProp::ram_reg> rg,
                                  const unsigned int i, const unsigned int v) {
  return std::make_shared<WfChipUpdRegProp::ram_reg>(ram_reg{
      update_nth<unsigned int>(
          std::move(i),
          (std::move(v) %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          rg->reg_main),
      rg->reg_status});
}

std::shared_ptr<WfChipUpdRegProp::ram_reg>
WfChipUpdRegProp::upd_stat_in_reg(std::shared_ptr<WfChipUpdRegProp::ram_reg> rg,
                                  const unsigned int i, const unsigned int v) {
  return std::make_shared<WfChipUpdRegProp::ram_reg>(ram_reg{
      rg->reg_main,
      update_nth<unsigned int>(
          std::move(i),
          (std::move(v) %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          rg->reg_status)});
}

std::shared_ptr<WfChipUpdRegProp::ram_reg> WfChipUpdRegProp::get_regRAM(
    const std::shared_ptr<WfChipUpdRegProp::ram_chip> &ch,
    const unsigned int r) {
  return ch->chip_regs->nth(r, empty_reg);
}

std::shared_ptr<WfChipUpdRegProp::ram_chip> WfChipUpdRegProp::upd_reg_in_chip(
    std::shared_ptr<WfChipUpdRegProp::ram_chip> ch, const unsigned int r,
    std::shared_ptr<WfChipUpdRegProp::ram_reg> rg) {
  return std::make_shared<WfChipUpdRegProp::ram_chip>(
      ram_chip{update_nth<std::shared_ptr<WfChipUpdRegProp::ram_reg>>(
                   std::move(r), std::move(rg), ch->chip_regs),
               ch->chip_port});
}

std::shared_ptr<WfChipUpdRegProp::ram_chip> WfChipUpdRegProp::upd_port_in_chip(
    std::shared_ptr<WfChipUpdRegProp::ram_chip> ch, const unsigned int v) {
  return std::make_shared<WfChipUpdRegProp::ram_chip>(ram_chip{
      std::move(ch)->chip_regs,
      (std::move(v) %
       ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1))});
}

std::shared_ptr<WfChipUpdRegProp::ram_chip> WfChipUpdRegProp::get_chip(
    const std::shared_ptr<WfChipUpdRegProp::ram_bank> &bk,
    const unsigned int c) {
  return bk->bank_chips->nth(c, empty_chip);
}

std::shared_ptr<WfChipUpdRegProp::ram_bank> WfChipUpdRegProp::upd_chip_in_bank(
    std::shared_ptr<WfChipUpdRegProp::ram_bank> bk, const unsigned int c,
    std::shared_ptr<WfChipUpdRegProp::ram_chip> ch) {
  return std::make_shared<WfChipUpdRegProp::ram_bank>(
      ram_bank{update_nth<std::shared_ptr<WfChipUpdRegProp::ram_chip>>(
          std::move(c), std::move(ch), std::move(bk)->bank_chips)});
}

std::shared_ptr<WfChipUpdRegProp::ram_bank> WfChipUpdRegProp::get_bank_from_sys(
    const std::shared_ptr<List<std::shared_ptr<WfChipUpdRegProp::ram_bank>>>
        &sys,
    const unsigned int b) {
  return sys->nth(b, empty_bank);
}

std::shared_ptr<List<std::shared_ptr<WfChipUpdRegProp::ram_bank>>>
WfChipUpdRegProp::upd_bank_in_sys(
    const std::shared_ptr<WfChipUpdRegProp::state> &s, const unsigned int b,
    const std::shared_ptr<WfChipUpdRegProp::ram_bank> &bk) {
  return update_nth<std::shared_ptr<WfChipUpdRegProp::ram_bank>>(b, bk,
                                                                 s->state_ram);
}

std::shared_ptr<WfChipUpdRegProp::ram_bank> WfChipUpdRegProp::current_bank(
    const std::shared_ptr<WfChipUpdRegProp::state> &s) {
  return get_bank_from_sys(s->state_ram, s->state_sel->sel_bank);
}

std::shared_ptr<WfChipUpdRegProp::ram_chip> WfChipUpdRegProp::current_chip(
    const std::shared_ptr<WfChipUpdRegProp::state> &s) {
  return get_chip(current_bank(s), s->state_sel->sel_chip);
}

std::shared_ptr<WfChipUpdRegProp::ram_reg> WfChipUpdRegProp::current_reg(
    const std::shared_ptr<WfChipUpdRegProp::state> &s) {
  return get_regRAM(current_chip(s), s->state_sel->sel_reg);
}

unsigned int WfChipUpdRegProp::ram_read_main(
    const std::shared_ptr<WfChipUpdRegProp::state> &s) {
  return get_main(current_reg(s), s->state_sel->sel_char);
}

std::shared_ptr<List<std::shared_ptr<WfChipUpdRegProp::ram_bank>>>
WfChipUpdRegProp::ram_write_main_sys(
    const std::shared_ptr<WfChipUpdRegProp::state> &s, const unsigned int v) {
  std::shared_ptr<WfChipUpdRegProp::ram_reg> rg = current_reg(s);
  std::shared_ptr<WfChipUpdRegProp::ram_chip> ch = current_chip(s);
  std::shared_ptr<WfChipUpdRegProp::ram_bank> bk = current_bank(s);
  std::shared_ptr<WfChipUpdRegProp::ram_reg> rg_ =
      upd_main_in_reg(std::move(rg), s->state_sel->sel_char, v);
  std::shared_ptr<WfChipUpdRegProp::ram_chip> ch_ =
      upd_reg_in_chip(std::move(ch), s->state_sel->sel_reg, std::move(rg_));
  std::shared_ptr<WfChipUpdRegProp::ram_bank> bk_ =
      upd_chip_in_bank(std::move(bk), s->state_sel->sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s->state_sel->sel_bank, std::move(bk_));
}

std::shared_ptr<List<std::shared_ptr<WfChipUpdRegProp::ram_bank>>>
WfChipUpdRegProp::ram_write_status_sys(
    const std::shared_ptr<WfChipUpdRegProp::state> &s, const unsigned int idx,
    const unsigned int v) {
  std::shared_ptr<WfChipUpdRegProp::ram_reg> rg = current_reg(s);
  std::shared_ptr<WfChipUpdRegProp::ram_chip> ch = current_chip(s);
  std::shared_ptr<WfChipUpdRegProp::ram_bank> bk = current_bank(s);
  std::shared_ptr<WfChipUpdRegProp::ram_reg> rg_ =
      upd_stat_in_reg(std::move(rg), idx, v);
  std::shared_ptr<WfChipUpdRegProp::ram_chip> ch_ =
      upd_reg_in_chip(std::move(ch), s->state_sel->sel_reg, std::move(rg_));
  std::shared_ptr<WfChipUpdRegProp::ram_bank> bk_ =
      upd_chip_in_bank(std::move(bk), s->state_sel->sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s->state_sel->sel_bank, std::move(bk_));
}

std::pair<std::optional<unsigned int>, std::shared_ptr<WfChipUpdRegProp::state>>
WfChipUpdRegProp::pop_stack(std::shared_ptr<WfChipUpdRegProp::state> s) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<WfChipUpdRegProp::state>> {
                   return std::make_pair(std::nullopt, std::move(s));
                 },
                 [&](const typename List<unsigned int>::cons _args)
                     -> std::pair<std::optional<unsigned int>,
                                  std::shared_ptr<WfChipUpdRegProp::state>> {
                   unsigned int x = _args._a0;
                   std::shared_ptr<List<unsigned int>> xs = _args._a1;
                   return std::make_pair(
                       std::make_optional<unsigned int>(std::move(x)),
                       std::make_shared<WfChipUpdRegProp::state>(
                           state{s->state_regs, s->state_acc, s->state_carry,
                                 s->state_pc, std::move(xs), s->state_ram,
                                 s->state_sel, s->state_rom}));
                 }},
      s->state_stack->v());
}
