#include "ram_accessor.h"

uint64_t RamAccessor::get_main(const RamAccessor::ram_reg &rg, uint64_t i) {
  return ListDef::template nth<uint64_t>(i, rg.reg_main, UINT64_C(0));
}

uint64_t RamAccessor::get_stat(const RamAccessor::ram_reg &rg, uint64_t i) {
  return ListDef::template nth<uint64_t>(i, rg.reg_status, UINT64_C(0));
}

RamAccessor::ram_reg
RamAccessor::upd_main_in_reg(const RamAccessor::ram_reg &rg, uint64_t i,
                             uint64_t v) {
  return ram_reg{update_nth<uint64_t>(i, (UINT64_C(16) ? v % UINT64_C(16) : v),
                                      rg.reg_main),
                 rg.reg_status};
}

RamAccessor::ram_reg
RamAccessor::upd_stat_in_reg(const RamAccessor::ram_reg &rg, uint64_t i,
                             uint64_t v) {
  return ram_reg{rg.reg_main,
                 update_nth<uint64_t>(i, (UINT64_C(16) ? v % UINT64_C(16) : v),
                                      rg.reg_status)};
}

RamAccessor::ram_reg RamAccessor::get_regRAM(const RamAccessor::ram_chip &ch,
                                             uint64_t r) {
  return ListDef::template nth<RamAccessor::ram_reg>(r, ch.chip_regs,
                                                     empty_reg);
}

RamAccessor::ram_chip
RamAccessor::upd_reg_in_chip(const RamAccessor::ram_chip &ch, uint64_t r,
                             const RamAccessor::ram_reg &rg) {
  return ram_chip{update_nth<RamAccessor::ram_reg>(r, rg, ch.chip_regs),
                  ch.chip_port};
}

RamAccessor::ram_chip
RamAccessor::upd_port_in_chip(const RamAccessor::ram_chip &ch, uint64_t v) {
  return ram_chip{ch.chip_regs, (UINT64_C(16) ? v % UINT64_C(16) : v)};
}

RamAccessor::ram_chip RamAccessor::get_chip(const RamAccessor::ram_bank &bk,
                                            uint64_t c) {
  return ListDef::template nth<RamAccessor::ram_chip>(c, bk.bank_chips,
                                                      empty_chip);
}

RamAccessor::ram_bank
RamAccessor::upd_chip_in_bank(const RamAccessor::ram_bank &bk, uint64_t c,
                              const RamAccessor::ram_chip &ch) {
  return ram_bank{update_nth<RamAccessor::ram_chip>(c, ch, bk.bank_chips)};
}

RamAccessor::ram_bank
RamAccessor::get_bank_from_sys(const List<RamAccessor::ram_bank> &sys,
                               uint64_t b) {
  return ListDef::template nth<RamAccessor::ram_bank>(b, sys, empty_bank);
}

List<RamAccessor::ram_bank>
RamAccessor::upd_bank_in_sys(const RamAccessor::state &s, uint64_t b,
                             const RamAccessor::ram_bank &bk) {
  return update_nth<RamAccessor::ram_bank>(b, bk, s.state_ram);
}

RamAccessor::ram_bank RamAccessor::current_bank(const RamAccessor::state &s) {
  return get_bank_from_sys(s.state_ram, s.state_sel.sel_bank);
}

RamAccessor::ram_chip RamAccessor::current_chip(const RamAccessor::state &s) {
  return get_chip(current_bank(s), s.state_sel.sel_chip);
}

RamAccessor::ram_reg RamAccessor::current_reg(const RamAccessor::state &s) {
  return get_regRAM(current_chip(s), s.state_sel.sel_reg);
}

uint64_t RamAccessor::ram_read_main(const RamAccessor::state &s) {
  return get_main(current_reg(s), s.state_sel.sel_char);
}

List<RamAccessor::ram_bank>
RamAccessor::ram_write_main_sys(const RamAccessor::state &s, uint64_t v) {
  RamAccessor::ram_reg rg = current_reg(s);
  RamAccessor::ram_chip ch = current_chip(s);
  RamAccessor::ram_bank bk = current_bank(s);
  RamAccessor::ram_reg rg_ =
      upd_main_in_reg(std::move(rg), s.state_sel.sel_char, v);
  RamAccessor::ram_chip ch_ =
      upd_reg_in_chip(std::move(ch), s.state_sel.sel_reg, std::move(rg_));
  RamAccessor::ram_bank bk_ =
      upd_chip_in_bank(std::move(bk), s.state_sel.sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s.state_sel.sel_bank, std::move(bk_));
}

List<RamAccessor::ram_bank>
RamAccessor::ram_write_status_sys(const RamAccessor::state &s, uint64_t idx,
                                  uint64_t v) {
  RamAccessor::ram_reg rg = current_reg(s);
  RamAccessor::ram_chip ch = current_chip(s);
  RamAccessor::ram_bank bk = current_bank(s);
  RamAccessor::ram_reg rg_ = upd_stat_in_reg(std::move(rg), idx, v);
  RamAccessor::ram_chip ch_ =
      upd_reg_in_chip(std::move(ch), s.state_sel.sel_reg, std::move(rg_));
  RamAccessor::ram_bank bk_ =
      upd_chip_in_bank(std::move(bk), s.state_sel.sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s.state_sel.sel_bank, std::move(bk_));
}
