#include "ram_state_ops.h"

RamStateOps::state RamStateOps::reset_state(const RamStateOps::state &s) {
  return state{s.state_regs,          UINT64_C(0), false,       UINT64_C(0),
               List<uint64_t>::nil(), s.state_ram, default_sel, s.state_rom};
}

uint64_t RamStateOps::get_main(const RamStateOps::ram_reg &rg, uint64_t i) {
  return ListDef::template nth<uint64_t>(i, rg.reg_main, UINT64_C(0));
}

uint64_t RamStateOps::get_stat(const RamStateOps::ram_reg &rg, uint64_t i) {
  return ListDef::template nth<uint64_t>(i, rg.reg_status, UINT64_C(0));
}

RamStateOps::ram_reg
RamStateOps::upd_main_in_reg(const RamStateOps::ram_reg &rg, uint64_t i,
                             uint64_t v) {
  return ram_reg{update_nth<uint64_t>(i, (UINT64_C(16) ? v % UINT64_C(16) : v),
                                      rg.reg_main),
                 rg.reg_status};
}

RamStateOps::ram_reg
RamStateOps::upd_stat_in_reg(const RamStateOps::ram_reg &rg, uint64_t i,
                             uint64_t v) {
  return ram_reg{rg.reg_main,
                 update_nth<uint64_t>(i, (UINT64_C(16) ? v % UINT64_C(16) : v),
                                      rg.reg_status)};
}

RamStateOps::ram_reg RamStateOps::get_regRAM(const RamStateOps::ram_chip &ch,
                                             uint64_t r) {
  return ListDef::template nth<RamStateOps::ram_reg>(r, ch.chip_regs,
                                                     empty_reg);
}

RamStateOps::ram_chip
RamStateOps::upd_reg_in_chip(const RamStateOps::ram_chip &ch, uint64_t r,
                             const RamStateOps::ram_reg &rg) {
  return ram_chip{update_nth<RamStateOps::ram_reg>(r, rg, ch.chip_regs),
                  ch.chip_port};
}

RamStateOps::ram_chip
RamStateOps::upd_port_in_chip(const RamStateOps::ram_chip &ch, uint64_t v) {
  return ram_chip{ch.chip_regs, (UINT64_C(16) ? v % UINT64_C(16) : v)};
}

RamStateOps::ram_chip RamStateOps::get_chip(const RamStateOps::ram_bank &bk,
                                            uint64_t c) {
  return ListDef::template nth<RamStateOps::ram_chip>(c, bk.bank_chips,
                                                      empty_chip);
}

RamStateOps::ram_bank
RamStateOps::upd_chip_in_bank(const RamStateOps::ram_bank &bk, uint64_t c,
                              const RamStateOps::ram_chip &ch) {
  return ram_bank{update_nth<RamStateOps::ram_chip>(c, ch, bk.bank_chips)};
}

RamStateOps::ram_bank
RamStateOps::get_bank_from_sys(const List<RamStateOps::ram_bank> &sys,
                               uint64_t b) {
  return ListDef::template nth<RamStateOps::ram_bank>(b, sys, empty_bank);
}

List<RamStateOps::ram_bank>
RamStateOps::upd_bank_in_sys(const RamStateOps::state &s, uint64_t b,
                             const RamStateOps::ram_bank &bk) {
  return update_nth<RamStateOps::ram_bank>(b, bk, s.state_ram);
}

RamStateOps::ram_bank RamStateOps::current_bank(const RamStateOps::state &s) {
  return get_bank_from_sys(s.state_ram, s.state_sel.sel_bank);
}

RamStateOps::ram_chip RamStateOps::current_chip(const RamStateOps::state &s) {
  return get_chip(current_bank(s), s.state_sel.sel_chip);
}

RamStateOps::ram_reg RamStateOps::current_reg(const RamStateOps::state &s) {
  return get_regRAM(current_chip(s), s.state_sel.sel_reg);
}

uint64_t RamStateOps::ram_read_main(const RamStateOps::state &s) {
  return get_main(current_reg(s), s.state_sel.sel_char);
}

List<RamStateOps::ram_bank>
RamStateOps::ram_write_main_sys(const RamStateOps::state &s, uint64_t v) {
  RamStateOps::ram_reg rg = current_reg(s);
  RamStateOps::ram_chip ch = current_chip(s);
  RamStateOps::ram_bank bk = current_bank(s);
  RamStateOps::ram_reg rg_ =
      upd_main_in_reg(std::move(rg), s.state_sel.sel_char, v);
  RamStateOps::ram_chip ch_ =
      upd_reg_in_chip(std::move(ch), s.state_sel.sel_reg, std::move(rg_));
  RamStateOps::ram_bank bk_ =
      upd_chip_in_bank(std::move(bk), s.state_sel.sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s.state_sel.sel_bank, std::move(bk_));
}

List<RamStateOps::ram_bank>
RamStateOps::ram_write_status_sys(const RamStateOps::state &s, uint64_t idx,
                                  uint64_t v) {
  RamStateOps::ram_reg rg = current_reg(s);
  RamStateOps::ram_chip ch = current_chip(s);
  RamStateOps::ram_bank bk = current_bank(s);
  RamStateOps::ram_reg rg_ = upd_stat_in_reg(std::move(rg), idx, v);
  RamStateOps::ram_chip ch_ =
      upd_reg_in_chip(std::move(ch), s.state_sel.sel_reg, std::move(rg_));
  RamStateOps::ram_bank bk_ =
      upd_chip_in_bank(std::move(bk), s.state_sel.sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s.state_sel.sel_bank, std::move(bk_));
}

std::pair<std::optional<uint64_t>, RamStateOps::state>
RamStateOps::pop_stack(RamStateOps::state s) {
  auto &&_sv = s.state_stack;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::make_pair(std::optional<uint64_t>(), std::move(s));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return std::make_pair(std::make_optional<uint64_t>(a0),
                          state{s.state_regs, s.state_acc, s.state_carry,
                                s.state_pc, *a1, s.state_ram, s.state_sel,
                                s.state_rom});
  }
}
