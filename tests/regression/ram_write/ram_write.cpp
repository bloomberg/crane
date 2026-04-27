#include <ram_write.h>

__attribute__((pure)) unsigned int
RamWrite::get_main(const RamWrite::ram_reg &rg, const unsigned int &i) {
  return ListDef::template nth<unsigned int>(i, rg.reg_main, 0u);
}

__attribute__((pure)) RamWrite::ram_reg
RamWrite::upd_main_in_reg(const RamWrite::ram_reg &rg, const unsigned int &i,
                          const unsigned int &v) {
  return ram_reg{update_nth<unsigned int>(i, (16u ? v % 16u : v), rg.reg_main),
                 rg.reg_status};
}

__attribute__((pure)) RamWrite::ram_reg
RamWrite::upd_stat_in_reg(const RamWrite::ram_reg &rg, const unsigned int &i,
                          const unsigned int &v) {
  return ram_reg{rg.reg_main, update_nth<unsigned int>(i, (16u ? v % 16u : v),
                                                       rg.reg_status)};
}

__attribute__((pure)) RamWrite::ram_reg
RamWrite::get_regRAM(const RamWrite::ram_chip &ch, const unsigned int &r) {
  return ListDef::template nth<RamWrite::ram_reg>(r, ch.chip_regs, empty_reg);
}

__attribute__((pure)) RamWrite::ram_chip
RamWrite::upd_reg_in_chip(const RamWrite::ram_chip &ch, const unsigned int &r,
                          const RamWrite::ram_reg &rg) {
  return ram_chip{update_nth<RamWrite::ram_reg>(r, rg, ch.chip_regs),
                  ch.chip_port};
}

__attribute__((pure)) RamWrite::ram_chip
RamWrite::get_chip(const RamWrite::ram_bank &bk, const unsigned int &c) {
  return ListDef::template nth<RamWrite::ram_chip>(c, bk.bank_chips,
                                                   empty_chip);
}

__attribute__((pure)) RamWrite::ram_bank
RamWrite::upd_chip_in_bank(const RamWrite::ram_bank &bk, const unsigned int &c,
                           const RamWrite::ram_chip &ch) {
  return ram_bank{update_nth<RamWrite::ram_chip>(c, ch, bk.bank_chips)};
}

__attribute__((pure)) RamWrite::ram_bank
RamWrite::get_bank_from_sys(const List<RamWrite::ram_bank> &sys,
                            const unsigned int &b) {
  return ListDef::template nth<RamWrite::ram_bank>(b, sys, empty_bank);
}

__attribute__((pure)) List<RamWrite::ram_bank>
RamWrite::upd_bank_in_sys(const RamWrite::state &s, const unsigned int &b,
                          const RamWrite::ram_bank &bk) {
  return update_nth<RamWrite::ram_bank>(b, bk, s.state_ram);
}

__attribute__((pure)) RamWrite::ram_bank
RamWrite::current_bank(const RamWrite::state &s) {
  return get_bank_from_sys(s.state_ram, s.state_sel.sel_bank);
}

__attribute__((pure)) RamWrite::ram_chip
RamWrite::current_chip(const RamWrite::state &s) {
  return get_chip(current_bank(s), s.state_sel.sel_chip);
}

__attribute__((pure)) RamWrite::ram_reg
RamWrite::current_reg(const RamWrite::state &s) {
  return get_regRAM(current_chip(s), s.state_sel.sel_reg);
}

__attribute__((pure)) unsigned int
RamWrite::ram_read_main(const RamWrite::state &s) {
  return get_main(current_reg(s), s.state_sel.sel_char);
}

__attribute__((pure)) List<RamWrite::ram_bank>
RamWrite::ram_write_main_sys(const RamWrite::state &s, const unsigned int &v) {
  RamWrite::ram_reg rg = current_reg(s);
  RamWrite::ram_chip ch = current_chip(s);
  RamWrite::ram_bank bk = current_bank(s);
  RamWrite::ram_reg rg_ = upd_main_in_reg(rg, s.state_sel.sel_char, v);
  RamWrite::ram_chip ch_ = upd_reg_in_chip(ch, s.state_sel.sel_reg, rg_);
  RamWrite::ram_bank bk_ = upd_chip_in_bank(bk, s.state_sel.sel_chip, ch_);
  return upd_bank_in_sys(s, s.state_sel.sel_bank, bk_);
}

__attribute__((pure)) List<RamWrite::ram_bank>
RamWrite::ram_write_status_sys(const RamWrite::state &s,
                               const unsigned int &idx, const unsigned int &v) {
  RamWrite::ram_reg rg = current_reg(s);
  RamWrite::ram_chip ch = current_chip(s);
  RamWrite::ram_bank bk = current_bank(s);
  RamWrite::ram_reg rg_ = upd_stat_in_reg(rg, idx, v);
  RamWrite::ram_chip ch_ = upd_reg_in_chip(ch, s.state_sel.sel_reg, rg_);
  RamWrite::ram_bank bk_ = upd_chip_in_bank(bk, s.state_sel.sel_chip, ch_);
  return upd_bank_in_sys(s, s.state_sel.sel_bank, bk_);
}
