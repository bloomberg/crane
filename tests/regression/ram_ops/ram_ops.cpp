#include "ram_ops.h"

RamOps::ram_bank_main RamOps::get_bank_main(const RamOps::state_main &s,
                                            uint64_t b) {
  return ListDef::template nth<RamOps::ram_bank_main>(
      b, s.ram_sys_main, ram_bank_main{List<RamOps::ram_chip_main>::nil()});
}

RamOps::ram_chip_main RamOps::get_chip_main(const RamOps::ram_bank_main &bk,
                                            uint64_t c) {
  return ListDef::template nth<RamOps::ram_chip_main>(
      c, bk.bank_chips_main, ram_chip_main{List<RamOps::ram_reg_main>::nil()});
}

RamOps::ram_reg_main RamOps::get_reg_main(const RamOps::ram_chip_main &ch,
                                          uint64_t r) {
  return ListDef::template nth<RamOps::ram_reg_main>(
      r, ch.chip_regs_main, ram_reg_main{List<uint64_t>::nil()});
}

RamOps::ram_reg_main RamOps::upd_main_in_reg(const RamOps::ram_reg_main &rg,
                                             uint64_t i, uint64_t v) {
  return ram_reg_main{update_nth_main<uint64_t>(
      i, (UINT64_C(16) ? v % UINT64_C(16) : v), rg.reg_main)};
}

RamOps::ram_chip_main
RamOps::upd_reg_in_chip_main(const RamOps::ram_chip_main &ch, uint64_t r,
                             const RamOps::ram_reg_main &rg) {
  return ram_chip_main{
      update_nth_main<RamOps::ram_reg_main>(r, rg, ch.chip_regs_main)};
}

RamOps::ram_bank_main
RamOps::upd_chip_in_bank_main(const RamOps::ram_bank_main &bk, uint64_t c,
                              const RamOps::ram_chip_main &ch) {
  return ram_bank_main{
      update_nth_main<RamOps::ram_chip_main>(c, ch, bk.bank_chips_main)};
}

List<RamOps::ram_bank_main>
RamOps::upd_bank_in_sys_main(const RamOps::state_main &s, uint64_t b,
                             const RamOps::ram_bank_main &bk) {
  return update_nth_main<RamOps::ram_bank_main>(b, bk, s.ram_sys_main);
}

List<RamOps::ram_bank_main>
RamOps::ram_write_main_sys(const RamOps::state_main &s, uint64_t v) {
  uint64_t b = s.cur_bank_main;
  uint64_t c = s.sel_chip_main;
  uint64_t r = s.sel_reg_main;
  uint64_t i = s.sel_char_main;
  RamOps::ram_bank_main bk = get_bank_main(s, b);
  RamOps::ram_chip_main ch = get_chip_main(bk, c);
  RamOps::ram_reg_main rg = get_reg_main(ch, r);
  RamOps::ram_reg_main rg_ = upd_main_in_reg(std::move(rg), i, v);
  RamOps::ram_chip_main ch_ =
      upd_reg_in_chip_main(std::move(ch), r, std::move(rg_));
  RamOps::ram_bank_main bk_ =
      upd_chip_in_bank_main(std::move(bk), c, std::move(ch_));
  return upd_bank_in_sys_main(s, b, std::move(bk_));
}

RamOps::bank_port RamOps::get_bank_port(const RamOps::state_port &s,
                                        uint64_t b) {
  return ListDef::template nth<RamOps::bank_port>(
      b, s.ram_sys_port, bank_port{List<RamOps::chip_port>::nil()});
}

RamOps::chip_port RamOps::get_chip_port(const RamOps::bank_port &bk,
                                        uint64_t c) {
  return ListDef::template nth<RamOps::chip_port>(c, bk.bank_chips_port,
                                                  chip_port{UINT64_C(0)});
}

RamOps::chip_port RamOps::upd_port_in_chip(const RamOps::chip_port &,
                                           uint64_t v) {
  return chip_port{(UINT64_C(16) ? v % UINT64_C(16) : v)};
}

RamOps::bank_port RamOps::upd_chip_in_bank_port(const RamOps::bank_port &bk,
                                                uint64_t c,
                                                const RamOps::chip_port &ch) {
  return bank_port{
      update_nth_port<RamOps::chip_port>(c, ch, bk.bank_chips_port)};
}

List<RamOps::bank_port>
RamOps::upd_bank_in_sys_port(const RamOps::state_port &s, uint64_t b,
                             const RamOps::bank_port &bk) {
  return update_nth_port<RamOps::bank_port>(b, bk, s.ram_sys_port);
}

List<RamOps::bank_port> RamOps::ram_write_port_sys(const RamOps::state_port &s,
                                                   uint64_t v) {
  uint64_t b = s.cur_bank_port;
  uint64_t c = s.sel_chip_port;
  RamOps::bank_port bk = get_bank_port(s, b);
  RamOps::chip_port ch = get_chip_port(bk, c);
  RamOps::chip_port ch_ = upd_port_in_chip(std::move(ch), v);
  RamOps::bank_port bk_ =
      upd_chip_in_bank_port(std::move(bk), c, std::move(ch_));
  return upd_bank_in_sys_port(s, b, std::move(bk_));
}

RamOps::ram_bank_status RamOps::get_bank_status(const RamOps::state_status &s,
                                                uint64_t b) {
  return ListDef::template nth<RamOps::ram_bank_status>(
      b, s.ram_sys_status,
      ram_bank_status{List<RamOps::ram_chip_status>::nil()});
}

RamOps::ram_chip_status
RamOps::get_chip_status(const RamOps::ram_bank_status &bk, uint64_t c) {
  return ListDef::template nth<RamOps::ram_chip_status>(
      c, bk.bank_chips_status,
      ram_chip_status{List<RamOps::ram_reg_status>::nil()});
}

RamOps::ram_reg_status RamOps::get_reg_status(const RamOps::ram_chip_status &ch,
                                              uint64_t r) {
  return ListDef::template nth<RamOps::ram_reg_status>(
      r, ch.chip_regs_status, ram_reg_status{List<uint64_t>::nil()});
}

RamOps::ram_reg_status
RamOps::upd_status_in_reg(const RamOps::ram_reg_status &rg, uint64_t i,
                          uint64_t v) {
  return ram_reg_status{update_nth_status<uint64_t>(
      i, (UINT64_C(16) ? v % UINT64_C(16) : v), rg.reg_status)};
}

RamOps::ram_chip_status
RamOps::upd_reg_in_chip_status(const RamOps::ram_chip_status &ch, uint64_t r,
                               const RamOps::ram_reg_status &rg) {
  return ram_chip_status{
      update_nth_status<RamOps::ram_reg_status>(r, rg, ch.chip_regs_status)};
}

RamOps::ram_bank_status
RamOps::upd_chip_in_bank_status(const RamOps::ram_bank_status &bk, uint64_t c,
                                const RamOps::ram_chip_status &ch) {
  return ram_bank_status{
      update_nth_status<RamOps::ram_chip_status>(c, ch, bk.bank_chips_status)};
}

List<RamOps::ram_bank_status>
RamOps::upd_bank_in_sys_status(const RamOps::state_status &s, uint64_t b,
                               const RamOps::ram_bank_status &bk) {
  return update_nth_status<RamOps::ram_bank_status>(b, bk, s.ram_sys_status);
}

List<RamOps::ram_bank_status>
RamOps::ram_write_status_sys(const RamOps::state_status &s, uint64_t idx,
                             uint64_t v) {
  uint64_t b = s.cur_bank_status;
  uint64_t c = s.sel_chip_status;
  uint64_t r = s.sel_reg_status;
  RamOps::ram_bank_status bk = get_bank_status(s, b);
  RamOps::ram_chip_status ch = get_chip_status(bk, c);
  RamOps::ram_reg_status rg = get_reg_status(ch, r);
  RamOps::ram_reg_status rg_ = upd_status_in_reg(std::move(rg), idx, v);
  RamOps::ram_chip_status ch_ =
      upd_reg_in_chip_status(std::move(ch), r, std::move(rg_));
  RamOps::ram_bank_status bk_ =
      upd_chip_in_bank_status(std::move(bk), c, std::move(ch_));
  return upd_bank_in_sys_status(s, b, std::move(bk_));
}

RamOps::ram_bank_sel RamOps::get_bank_sel(const RamOps::state_sel &s,
                                          uint64_t b) {
  return ListDef::template nth<RamOps::ram_bank_sel>(b, s.ram_sys_sel,
                                                     empty_bank_sel);
}

RamOps::ram_chip_sel RamOps::get_chip_sel(const RamOps::ram_bank_sel &bk,
                                          uint64_t c) {
  return ListDef::template nth<RamOps::ram_chip_sel>(c, bk.bank_chips_sel,
                                                     empty_chip_sel);
}

RamOps::ram_reg_sel RamOps::get_regRAM(const RamOps::ram_chip_sel &ch,
                                       uint64_t r) {
  return ListDef::template nth<RamOps::ram_reg_sel>(r, ch.chip_regs_sel,
                                                    empty_reg_sel);
}

uint64_t RamOps::get_main_sel(const RamOps::ram_reg_sel &rg, uint64_t i) {
  return ListDef::template nth<uint64_t>(i, rg.reg_main_sel, UINT64_C(0));
}

uint64_t RamOps::ram_read_main(const RamOps::state_sel &s) {
  RamOps::ram_bank_sel bk = get_bank_sel(s, s.cur_bank_sel);
  RamOps::ram_chip_sel ch = get_chip_sel(std::move(bk), s.sel_ram.sel_chip);
  RamOps::ram_reg_sel rg = get_regRAM(std::move(ch), s.sel_ram.sel_reg);
  return get_main_sel(std::move(rg), s.sel_ram.sel_char);
}

RamOps::ram_bank_nested RamOps::get_bank_nested(const RamOps::state_nested &s,
                                                uint64_t b) {
  return ListDef::template nth<RamOps::ram_bank_nested>(b, s.ram_sys_nested,
                                                        empty_bank_nested);
}

RamOps::ram_chip_nested
RamOps::get_chip_nested(const RamOps::ram_bank_nested &bk, uint64_t c) {
  return ListDef::template nth<RamOps::ram_chip_nested>(c, bk.bank_chips_nested,
                                                        empty_chip_nested);
}

RamOps::ram_reg_nested
RamOps::get_regRAM_nested(const RamOps::ram_chip_nested &ch, uint64_t r) {
  return ListDef::template nth<RamOps::ram_reg_nested>(r, ch.chip_regs_nested,
                                                       empty_reg_nested);
}

uint64_t RamOps::get_main_nested(const RamOps::ram_reg_nested &rg, uint64_t i) {
  return ListDef::template nth<uint64_t>(i, rg.reg_main_nested, UINT64_C(0));
}

uint64_t RamOps::ram_read_main_nested(const RamOps::state_nested &s) {
  RamOps::ram_bank_nested bk = get_bank_nested(s, s.cur_bank_nested);
  RamOps::ram_chip_nested ch =
      get_chip_nested(std::move(bk), s.sel_ram_nested.sel_chip_nested);
  RamOps::ram_reg_nested rg =
      get_regRAM_nested(std::move(ch), s.sel_ram_nested.sel_reg_nested);
  return get_main_nested(std::move(rg), s.sel_ram_nested.sel_char_nested);
}

RamOps::reg_frame RamOps::upd_main_in_reg_frame(const List<uint64_t> &rg,
                                                uint64_t i, uint64_t v) {
  return update_nth_frame<uint64_t>(i, v, rg);
}

RamOps::chip_frame RamOps::upd_reg_in_chip_frame(const List<List<uint64_t>> &ch,
                                                 uint64_t r,
                                                 const List<uint64_t> &rg) {
  return update_nth_frame<RamOps::reg_frame>(r, rg, ch);
}

RamOps::bank_frame
RamOps::upd_chip_in_bank_frame(const List<List<List<uint64_t>>> &bk, uint64_t c,
                               const List<List<uint64_t>> &ch) {
  return update_nth_frame<RamOps::chip_frame>(c, ch, bk);
}

List<uint64_t>
RamOps::ram_write_main_sys_preserve(const RamOps::state_preserve &s,
                                    uint64_t v) {
  return update_nth_preserve<uint64_t>(s.cur_bank_preserve, v,
                                       s.ram_sys_preserve);
}

RamOps::state_preserve RamOps::execute_write(const RamOps::state_preserve &s,
                                             uint64_t v) {
  return state_preserve{ram_write_main_sys_preserve(s, v), s.cur_bank_preserve};
}

bool RamOps::ram_addr_disjointb(uint64_t b1, uint64_t c1, uint64_t r1,
                                uint64_t i1, uint64_t b2, uint64_t c2,
                                uint64_t r2, uint64_t i2) {
  return !((((b1 == b2 && c1 == c2) && r1 == r2) && i1 == i2));
}

RamOps::bank_nested_bank RamOps::get_bank0(const RamOps::state_nested_bank &s) {
  return ListDef::template nth<RamOps::bank_nested_bank>(
      UINT64_C(0), s.banks_,
      bank_nested_bank{List<RamOps::chip_nested_bank>::nil()});
}

RamOps::chip_nested_bank RamOps::get_chip0(const RamOps::bank_nested_bank &b) {
  return ListDef::template nth<RamOps::chip_nested_bank>(
      UINT64_C(0), b.chips_,
      chip_nested_bank{List<RamOps::reg_nested_bank>::nil()});
}

RamOps::reg_nested_bank RamOps::get_reg0(const RamOps::chip_nested_bank &c) {
  return ListDef::template nth<RamOps::reg_nested_bank>(
      UINT64_C(0), c.regs_, reg_nested_bank{List<uint64_t>::nil()});
}

RamOps::state_nested_bank
RamOps::write_status0(const RamOps::state_nested_bank &s, uint64_t v) {
  RamOps::bank_nested_bank b = get_bank0(s);
  RamOps::chip_nested_bank c = get_chip0(b);
  RamOps::reg_nested_bank r = get_reg0(c);
  RamOps::reg_nested_bank r_ = reg_nested_bank{
      update_nth_nested_bank<uint64_t>(UINT64_C(0), v, r.status_)};
  RamOps::chip_nested_bank c_ =
      chip_nested_bank{update_nth_nested_bank<RamOps::reg_nested_bank>(
          UINT64_C(0), r_, c.regs_)};
  RamOps::bank_nested_bank b_ =
      bank_nested_bank{update_nth_nested_bank<RamOps::chip_nested_bank>(
          UINT64_C(0), c_, b.chips_)};
  return state_nested_bank{update_nth_nested_bank<RamOps::bank_nested_bank>(
      UINT64_C(0), b_, s.banks_)};
}

uint64_t RamOps::read_status0(const RamOps::state_nested_bank &s) {
  RamOps::bank_nested_bank b = get_bank0(s);
  RamOps::chip_nested_bank c = get_chip0(std::move(b));
  RamOps::reg_nested_bank r = get_reg0(std::move(c));
  return ListDef::template nth<uint64_t>(UINT64_C(0), std::move(r).status_,
                                         UINT64_C(0));
}

uint64_t RamOps::score(RamOps::Item x) {
  switch (x) {
  case Item::S_: {
    return UINT64_C(1);
  }
  case Item::S_0: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}
