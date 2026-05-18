#include "ram_write.h"

uint64_t RamWrite::get_main(const RamWrite::ram_reg &rg, uint64_t i) {
  return ListDef::template nth<uint64_t>(i, rg.reg_main, UINT64_C(0));
}

RamWrite::ram_reg RamWrite::upd_main_in_reg(const RamWrite::ram_reg &rg,
                                            uint64_t i, uint64_t v) {
  return ram_reg{update_nth<uint64_t>(i, (UINT64_C(16) ? v % UINT64_C(16) : v),
                                      rg.reg_main),
                 rg.reg_status};
}

RamWrite::ram_reg RamWrite::upd_stat_in_reg(const RamWrite::ram_reg &rg,
                                            uint64_t i, uint64_t v) {
  return ram_reg{rg.reg_main,
                 update_nth<uint64_t>(i, (UINT64_C(16) ? v % UINT64_C(16) : v),
                                      rg.reg_status)};
}

RamWrite::ram_reg RamWrite::get_regRAM(const RamWrite::ram_chip &ch,
                                       uint64_t r) {
  return ListDef::template nth<RamWrite::ram_reg>(r, ch.chip_regs, empty_reg);
}

RamWrite::ram_chip RamWrite::upd_reg_in_chip(const RamWrite::ram_chip &ch,
                                             uint64_t r,
                                             const RamWrite::ram_reg &rg) {
  return ram_chip{update_nth<RamWrite::ram_reg>(r, rg, ch.chip_regs),
                  ch.chip_port};
}

RamWrite::ram_chip RamWrite::get_chip(const RamWrite::ram_bank &bk,
                                      uint64_t c) {
  return ListDef::template nth<RamWrite::ram_chip>(c, bk.bank_chips,
                                                   empty_chip);
}

RamWrite::ram_bank RamWrite::upd_chip_in_bank(const RamWrite::ram_bank &bk,
                                              uint64_t c,
                                              const RamWrite::ram_chip &ch) {
  return ram_bank{update_nth<RamWrite::ram_chip>(c, ch, bk.bank_chips)};
}

RamWrite::ram_bank
RamWrite::get_bank_from_sys(const List<RamWrite::ram_bank> &sys, uint64_t b) {
  return ListDef::template nth<RamWrite::ram_bank>(b, sys, empty_bank);
}

List<RamWrite::ram_bank>
RamWrite::upd_bank_in_sys(const RamWrite::state &s, uint64_t b,
                          const RamWrite::ram_bank &bk) {
  return update_nth<RamWrite::ram_bank>(b, bk, s.state_ram);
}

RamWrite::ram_bank RamWrite::current_bank(const RamWrite::state &s) {
  return get_bank_from_sys(s.state_ram, s.state_sel.sel_bank);
}

RamWrite::ram_chip RamWrite::current_chip(const RamWrite::state &s) {
  return get_chip(current_bank(s), s.state_sel.sel_chip);
}

RamWrite::ram_reg RamWrite::current_reg(const RamWrite::state &s) {
  return get_regRAM(current_chip(s), s.state_sel.sel_reg);
}

uint64_t RamWrite::ram_read_main(const RamWrite::state &s) {
  return get_main(current_reg(s), s.state_sel.sel_char);
}

List<RamWrite::ram_bank> RamWrite::ram_write_main_sys(const RamWrite::state &s,
                                                      uint64_t v) {
  RamWrite::ram_reg rg = current_reg(s);
  RamWrite::ram_chip ch = current_chip(s);
  RamWrite::ram_bank bk = current_bank(s);
  RamWrite::ram_reg rg_ =
      upd_main_in_reg(std::move(rg), s.state_sel.sel_char, v);
  RamWrite::ram_chip ch_ =
      upd_reg_in_chip(std::move(ch), s.state_sel.sel_reg, std::move(rg_));
  RamWrite::ram_bank bk_ =
      upd_chip_in_bank(std::move(bk), s.state_sel.sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s.state_sel.sel_bank, std::move(bk_));
}

List<RamWrite::ram_bank>
RamWrite::ram_write_status_sys(const RamWrite::state &s, uint64_t idx,
                               uint64_t v) {
  RamWrite::ram_reg rg = current_reg(s);
  RamWrite::ram_chip ch = current_chip(s);
  RamWrite::ram_bank bk = current_bank(s);
  RamWrite::ram_reg rg_ = upd_stat_in_reg(std::move(rg), idx, v);
  RamWrite::ram_chip ch_ =
      upd_reg_in_chip(std::move(ch), s.state_sel.sel_reg, std::move(rg_));
  RamWrite::ram_bank bk_ =
      upd_chip_in_bank(std::move(bk), s.state_sel.sel_chip, std::move(ch_));
  return upd_bank_in_sys(s, s.state_sel.sel_bank, std::move(bk_));
}
