#include <ram_accessor.h>

__attribute__((pure)) unsigned int
RamAccessor::get_main(const RamAccessor::ram_reg &rg, const unsigned int &i) {
  return ListDef::template nth<unsigned int>(i, rg.reg_main, 0u);
}

__attribute__((pure)) unsigned int
RamAccessor::get_stat(const RamAccessor::ram_reg &rg, const unsigned int &i) {
  return ListDef::template nth<unsigned int>(i, rg.reg_status, 0u);
}

__attribute__((pure)) RamAccessor::ram_reg
RamAccessor::upd_main_in_reg(const RamAccessor::ram_reg &rg,
                             const unsigned int &i, const unsigned int &v) {
  return ram_reg{update_nth<unsigned int>(i, (16u ? v % 16u : v), rg.reg_main),
                 rg.reg_status};
}

__attribute__((pure)) RamAccessor::ram_reg
RamAccessor::upd_stat_in_reg(const RamAccessor::ram_reg &rg,
                             const unsigned int &i, const unsigned int &v) {
  return ram_reg{rg.reg_main, update_nth<unsigned int>(i, (16u ? v % 16u : v),
                                                       rg.reg_status)};
}

__attribute__((pure)) RamAccessor::ram_reg
RamAccessor::get_regRAM(const RamAccessor::ram_chip &ch,
                        const unsigned int &r) {
  return ListDef::template nth<RamAccessor::ram_reg>(r, ch.chip_regs,
                                                     empty_reg);
}

__attribute__((pure)) RamAccessor::ram_chip
RamAccessor::upd_reg_in_chip(const RamAccessor::ram_chip &ch,
                             const unsigned int &r,
                             const RamAccessor::ram_reg &rg) {
  return ram_chip{update_nth<RamAccessor::ram_reg>(r, rg, ch.chip_regs),
                  ch.chip_port};
}

__attribute__((pure)) RamAccessor::ram_chip
RamAccessor::upd_port_in_chip(const RamAccessor::ram_chip &ch,
                              const unsigned int &v) {
  return ram_chip{ch.chip_regs, (16u ? v % 16u : v)};
}

__attribute__((pure)) RamAccessor::ram_chip
RamAccessor::get_chip(const RamAccessor::ram_bank &bk, const unsigned int &c) {
  return ListDef::template nth<RamAccessor::ram_chip>(c, bk.bank_chips,
                                                      empty_chip);
}

__attribute__((pure)) RamAccessor::ram_bank
RamAccessor::upd_chip_in_bank(const RamAccessor::ram_bank &bk,
                              const unsigned int &c,
                              const RamAccessor::ram_chip &ch) {
  return ram_bank{update_nth<RamAccessor::ram_chip>(c, ch, bk.bank_chips)};
}

__attribute__((pure)) RamAccessor::ram_bank
RamAccessor::get_bank_from_sys(const List<RamAccessor::ram_bank> &sys,
                               const unsigned int &b) {
  return ListDef::template nth<RamAccessor::ram_bank>(b, sys, empty_bank);
}

__attribute__((pure)) List<RamAccessor::ram_bank>
RamAccessor::upd_bank_in_sys(const RamAccessor::state &s, const unsigned int &b,
                             const RamAccessor::ram_bank &bk) {
  return update_nth<RamAccessor::ram_bank>(b, bk, s.state_ram);
}

__attribute__((pure)) RamAccessor::ram_bank
RamAccessor::current_bank(const RamAccessor::state &s) {
  return get_bank_from_sys(s.state_ram, s.state_sel.sel_bank);
}

__attribute__((pure)) RamAccessor::ram_chip
RamAccessor::current_chip(const RamAccessor::state &s) {
  return get_chip(current_bank(s), s.state_sel.sel_chip);
}

__attribute__((pure)) RamAccessor::ram_reg
RamAccessor::current_reg(const RamAccessor::state &s) {
  return get_regRAM(current_chip(s), s.state_sel.sel_reg);
}

__attribute__((pure)) unsigned int
RamAccessor::ram_read_main(const RamAccessor::state &s) {
  return get_main(current_reg(s), s.state_sel.sel_char);
}

__attribute__((pure)) List<RamAccessor::ram_bank>
RamAccessor::ram_write_main_sys(const RamAccessor::state &s,
                                const unsigned int &v) {
  RamAccessor::ram_reg rg = current_reg(s);
  RamAccessor::ram_chip ch = current_chip(s);
  RamAccessor::ram_bank bk = current_bank(s);
  RamAccessor::ram_reg rg_ = upd_main_in_reg(rg, s.state_sel.sel_char, v);
  RamAccessor::ram_chip ch_ = upd_reg_in_chip(ch, s.state_sel.sel_reg, rg_);
  RamAccessor::ram_bank bk_ = upd_chip_in_bank(bk, s.state_sel.sel_chip, ch_);
  return upd_bank_in_sys(s, s.state_sel.sel_bank, bk_);
}

__attribute__((pure)) List<RamAccessor::ram_bank>
RamAccessor::ram_write_status_sys(const RamAccessor::state &s,
                                  const unsigned int &idx,
                                  const unsigned int &v) {
  RamAccessor::ram_reg rg = current_reg(s);
  RamAccessor::ram_chip ch = current_chip(s);
  RamAccessor::ram_bank bk = current_bank(s);
  RamAccessor::ram_reg rg_ = upd_stat_in_reg(rg, idx, v);
  RamAccessor::ram_chip ch_ = upd_reg_in_chip(ch, s.state_sel.sel_reg, rg_);
  RamAccessor::ram_bank bk_ = upd_chip_in_bank(bk, s.state_sel.sel_chip, ch_);
  return upd_bank_in_sys(s, s.state_sel.sel_bank, bk_);
}
