#include <ram_ops.h>

__attribute__((pure)) RamOps::ram_bank_main
RamOps::get_bank_main(const RamOps::state_main &s, const unsigned int &b) {
  return ListDef::template nth<RamOps::ram_bank_main>(
      b, s.ram_sys_main, ram_bank_main{List<RamOps::ram_chip_main>::nil()});
}

__attribute__((pure)) RamOps::ram_chip_main
RamOps::get_chip_main(const RamOps::ram_bank_main &bk, const unsigned int &c) {
  return ListDef::template nth<RamOps::ram_chip_main>(
      c, bk.bank_chips_main, ram_chip_main{List<RamOps::ram_reg_main>::nil()});
}

__attribute__((pure)) RamOps::ram_reg_main
RamOps::get_reg_main(const RamOps::ram_chip_main &ch, const unsigned int &r) {
  return ListDef::template nth<RamOps::ram_reg_main>(
      r, ch.chip_regs_main, ram_reg_main{List<unsigned int>::nil()});
}

__attribute__((pure)) RamOps::ram_reg_main
RamOps::upd_main_in_reg(const RamOps::ram_reg_main &rg, const unsigned int &i,
                        const unsigned int &v) {
  return ram_reg_main{
      update_nth_main<unsigned int>(i, (16u ? v % 16u : v), rg.reg_main)};
}

__attribute__((pure)) RamOps::ram_chip_main
RamOps::upd_reg_in_chip_main(const RamOps::ram_chip_main &ch,
                             const unsigned int &r,
                             const RamOps::ram_reg_main &rg) {
  return ram_chip_main{
      update_nth_main<RamOps::ram_reg_main>(r, rg, ch.chip_regs_main)};
}

__attribute__((pure)) RamOps::ram_bank_main
RamOps::upd_chip_in_bank_main(const RamOps::ram_bank_main &bk,
                              const unsigned int &c,
                              const RamOps::ram_chip_main &ch) {
  return ram_bank_main{
      update_nth_main<RamOps::ram_chip_main>(c, ch, bk.bank_chips_main)};
}

__attribute__((pure)) List<RamOps::ram_bank_main>
RamOps::upd_bank_in_sys_main(const RamOps::state_main &s, const unsigned int &b,
                             const RamOps::ram_bank_main &bk) {
  return update_nth_main<RamOps::ram_bank_main>(b, bk, s.ram_sys_main);
}

__attribute__((pure)) List<RamOps::ram_bank_main>
RamOps::ram_write_main_sys(const RamOps::state_main &s, const unsigned int &v) {
  unsigned int b = s.cur_bank_main;
  unsigned int c = s.sel_chip_main;
  unsigned int r = s.sel_reg_main;
  unsigned int i = s.sel_char_main;
  RamOps::ram_bank_main bk = get_bank_main(s, b);
  RamOps::ram_chip_main ch = get_chip_main(bk, c);
  RamOps::ram_reg_main rg = get_reg_main(ch, r);
  RamOps::ram_reg_main rg_ = upd_main_in_reg(rg, i, v);
  RamOps::ram_chip_main ch_ = upd_reg_in_chip_main(ch, r, rg_);
  RamOps::ram_bank_main bk_ = upd_chip_in_bank_main(bk, c, ch_);
  return upd_bank_in_sys_main(s, b, bk_);
}

__attribute__((pure)) RamOps::bank_port
RamOps::get_bank_port(const RamOps::state_port &s, const unsigned int &b) {
  return ListDef::template nth<RamOps::bank_port>(
      b, s.ram_sys_port, bank_port{List<RamOps::chip_port>::nil()});
}

__attribute__((pure)) RamOps::chip_port
RamOps::get_chip_port(const RamOps::bank_port &bk, const unsigned int &c) {
  return ListDef::template nth<RamOps::chip_port>(c, bk.bank_chips_port,
                                                  chip_port{0u});
}

__attribute__((pure)) RamOps::chip_port
RamOps::upd_port_in_chip(const RamOps::chip_port &, const unsigned int &v) {
  return chip_port{(16u ? v % 16u : v)};
}

__attribute__((pure)) RamOps::bank_port
RamOps::upd_chip_in_bank_port(const RamOps::bank_port &bk,
                              const unsigned int &c,
                              const RamOps::chip_port &ch) {
  return bank_port{
      update_nth_port<RamOps::chip_port>(c, ch, bk.bank_chips_port)};
}

__attribute__((pure)) List<RamOps::bank_port>
RamOps::upd_bank_in_sys_port(const RamOps::state_port &s, const unsigned int &b,
                             const RamOps::bank_port &bk) {
  return update_nth_port<RamOps::bank_port>(b, bk, s.ram_sys_port);
}

__attribute__((pure)) List<RamOps::bank_port>
RamOps::ram_write_port_sys(const RamOps::state_port &s, const unsigned int &v) {
  unsigned int b = s.cur_bank_port;
  unsigned int c = s.sel_chip_port;
  RamOps::bank_port bk = get_bank_port(s, b);
  RamOps::chip_port ch = get_chip_port(bk, c);
  RamOps::chip_port ch_ = upd_port_in_chip(ch, v);
  RamOps::bank_port bk_ = upd_chip_in_bank_port(bk, c, ch_);
  return upd_bank_in_sys_port(s, b, bk_);
}

__attribute__((pure)) RamOps::ram_bank_status
RamOps::get_bank_status(const RamOps::state_status &s, const unsigned int &b) {
  return ListDef::template nth<RamOps::ram_bank_status>(
      b, s.ram_sys_status,
      ram_bank_status{List<RamOps::ram_chip_status>::nil()});
}

__attribute__((pure)) RamOps::ram_chip_status
RamOps::get_chip_status(const RamOps::ram_bank_status &bk,
                        const unsigned int &c) {
  return ListDef::template nth<RamOps::ram_chip_status>(
      c, bk.bank_chips_status,
      ram_chip_status{List<RamOps::ram_reg_status>::nil()});
}

__attribute__((pure)) RamOps::ram_reg_status
RamOps::get_reg_status(const RamOps::ram_chip_status &ch,
                       const unsigned int &r) {
  return ListDef::template nth<RamOps::ram_reg_status>(
      r, ch.chip_regs_status, ram_reg_status{List<unsigned int>::nil()});
}

__attribute__((pure)) RamOps::ram_reg_status
RamOps::upd_status_in_reg(const RamOps::ram_reg_status &rg,
                          const unsigned int &i, const unsigned int &v) {
  return ram_reg_status{
      update_nth_status<unsigned int>(i, (16u ? v % 16u : v), rg.reg_status)};
}

__attribute__((pure)) RamOps::ram_chip_status
RamOps::upd_reg_in_chip_status(const RamOps::ram_chip_status &ch,
                               const unsigned int &r,
                               const RamOps::ram_reg_status &rg) {
  return ram_chip_status{
      update_nth_status<RamOps::ram_reg_status>(r, rg, ch.chip_regs_status)};
}

__attribute__((pure)) RamOps::ram_bank_status
RamOps::upd_chip_in_bank_status(const RamOps::ram_bank_status &bk,
                                const unsigned int &c,
                                const RamOps::ram_chip_status &ch) {
  return ram_bank_status{
      update_nth_status<RamOps::ram_chip_status>(c, ch, bk.bank_chips_status)};
}

__attribute__((pure)) List<RamOps::ram_bank_status>
RamOps::upd_bank_in_sys_status(const RamOps::state_status &s,
                               const unsigned int &b,
                               const RamOps::ram_bank_status &bk) {
  return update_nth_status<RamOps::ram_bank_status>(b, bk, s.ram_sys_status);
}

__attribute__((pure)) List<RamOps::ram_bank_status>
RamOps::ram_write_status_sys(const RamOps::state_status &s,
                             const unsigned int &idx, const unsigned int &v) {
  unsigned int b = s.cur_bank_status;
  unsigned int c = s.sel_chip_status;
  unsigned int r = s.sel_reg_status;
  RamOps::ram_bank_status bk = get_bank_status(s, b);
  RamOps::ram_chip_status ch = get_chip_status(bk, c);
  RamOps::ram_reg_status rg = get_reg_status(ch, r);
  RamOps::ram_reg_status rg_ = upd_status_in_reg(rg, idx, v);
  RamOps::ram_chip_status ch_ = upd_reg_in_chip_status(ch, r, rg_);
  RamOps::ram_bank_status bk_ = upd_chip_in_bank_status(bk, c, ch_);
  return upd_bank_in_sys_status(s, b, bk_);
}

__attribute__((pure)) RamOps::ram_bank_sel
RamOps::get_bank_sel(const RamOps::state_sel &s, const unsigned int &b) {
  return ListDef::template nth<RamOps::ram_bank_sel>(b, s.ram_sys_sel,
                                                     empty_bank_sel);
}

__attribute__((pure)) RamOps::ram_chip_sel
RamOps::get_chip_sel(const RamOps::ram_bank_sel &bk, const unsigned int &c) {
  return ListDef::template nth<RamOps::ram_chip_sel>(c, bk.bank_chips_sel,
                                                     empty_chip_sel);
}

__attribute__((pure)) RamOps::ram_reg_sel
RamOps::get_regRAM(const RamOps::ram_chip_sel &ch, const unsigned int &r) {
  return ListDef::template nth<RamOps::ram_reg_sel>(r, ch.chip_regs_sel,
                                                    empty_reg_sel);
}

__attribute__((pure)) unsigned int
RamOps::get_main_sel(const RamOps::ram_reg_sel &rg, const unsigned int &i) {
  return ListDef::template nth<unsigned int>(i, rg.reg_main_sel, 0u);
}

__attribute__((pure)) unsigned int
RamOps::ram_read_main(const RamOps::state_sel &s) {
  RamOps::ram_bank_sel bk = get_bank_sel(s, s.cur_bank_sel);
  RamOps::ram_chip_sel ch = get_chip_sel(bk, s.sel_ram.sel_chip);
  RamOps::ram_reg_sel rg = get_regRAM(ch, s.sel_ram.sel_reg);
  return get_main_sel(rg, s.sel_ram.sel_char);
}

__attribute__((pure)) RamOps::ram_bank_nested
RamOps::get_bank_nested(const RamOps::state_nested &s, const unsigned int &b) {
  return ListDef::template nth<RamOps::ram_bank_nested>(b, s.ram_sys_nested,
                                                        empty_bank_nested);
}

__attribute__((pure)) RamOps::ram_chip_nested
RamOps::get_chip_nested(const RamOps::ram_bank_nested &bk,
                        const unsigned int &c) {
  return ListDef::template nth<RamOps::ram_chip_nested>(c, bk.bank_chips_nested,
                                                        empty_chip_nested);
}

__attribute__((pure)) RamOps::ram_reg_nested
RamOps::get_regRAM_nested(const RamOps::ram_chip_nested &ch,
                          const unsigned int &r) {
  return ListDef::template nth<RamOps::ram_reg_nested>(r, ch.chip_regs_nested,
                                                       empty_reg_nested);
}

__attribute__((pure)) unsigned int
RamOps::get_main_nested(const RamOps::ram_reg_nested &rg,
                        const unsigned int &i) {
  return ListDef::template nth<unsigned int>(i, rg.reg_main_nested, 0u);
}

__attribute__((pure)) unsigned int
RamOps::ram_read_main_nested(const RamOps::state_nested &s) {
  RamOps::ram_bank_nested bk = get_bank_nested(s, s.cur_bank_nested);
  RamOps::ram_chip_nested ch =
      get_chip_nested(bk, s.sel_ram_nested.sel_chip_nested);
  RamOps::ram_reg_nested rg =
      get_regRAM_nested(ch, s.sel_ram_nested.sel_reg_nested);
  return get_main_nested(rg, s.sel_ram_nested.sel_char_nested);
}

__attribute__((pure)) RamOps::reg_frame
RamOps::upd_main_in_reg_frame(const List<unsigned int> &rg,
                              const unsigned int &i, const unsigned int &v) {
  return update_nth_frame<unsigned int>(i, v, rg);
}

__attribute__((pure)) RamOps::chip_frame
RamOps::upd_reg_in_chip_frame(const List<List<unsigned int>> &ch,
                              const unsigned int &r,
                              const List<unsigned int> &rg) {
  return update_nth_frame<RamOps::reg_frame>(r, rg, ch);
}

__attribute__((pure)) RamOps::bank_frame
RamOps::upd_chip_in_bank_frame(const List<List<List<unsigned int>>> &bk,
                               const unsigned int &c,
                               const List<List<unsigned int>> &ch) {
  return update_nth_frame<RamOps::chip_frame>(c, ch, bk);
}

__attribute__((pure)) List<unsigned int>
RamOps::ram_write_main_sys_preserve(const RamOps::state_preserve &s,
                                    const unsigned int &v) {
  return update_nth_preserve<unsigned int>(s.cur_bank_preserve, v,
                                           s.ram_sys_preserve);
}

__attribute__((pure)) RamOps::state_preserve
RamOps::execute_write(const RamOps::state_preserve &s, const unsigned int &v) {
  return state_preserve{ram_write_main_sys_preserve(s, v), s.cur_bank_preserve};
}

__attribute__((pure)) bool
RamOps::ram_addr_disjointb(const unsigned int &b1, const unsigned int &c1,
                           const unsigned int &r1, const unsigned int &i1,
                           const unsigned int &b2, const unsigned int &c2,
                           const unsigned int &r2, const unsigned int &i2) {
  return !((((b1 == b2 && c1 == c2) && r1 == r2) && i1 == i2));
}

__attribute__((pure)) RamOps::bank_nested_bank
RamOps::get_bank0(const RamOps::state_nested_bank &s) {
  return ListDef::template nth<RamOps::bank_nested_bank>(
      0u, s.banks_, bank_nested_bank{List<RamOps::chip_nested_bank>::nil()});
}

__attribute__((pure)) RamOps::chip_nested_bank
RamOps::get_chip0(const RamOps::bank_nested_bank &b) {
  return ListDef::template nth<RamOps::chip_nested_bank>(
      0u, b.chips_, chip_nested_bank{List<RamOps::reg_nested_bank>::nil()});
}

__attribute__((pure)) RamOps::reg_nested_bank
RamOps::get_reg0(const RamOps::chip_nested_bank &c) {
  return ListDef::template nth<RamOps::reg_nested_bank>(
      0u, c.regs_, reg_nested_bank{List<unsigned int>::nil()});
}

__attribute__((pure)) RamOps::state_nested_bank
RamOps::write_status0(const RamOps::state_nested_bank &s,
                      const unsigned int &v) {
  RamOps::bank_nested_bank b = get_bank0(s);
  RamOps::chip_nested_bank c = get_chip0(b);
  RamOps::reg_nested_bank r = get_reg0(c);
  RamOps::reg_nested_bank r_ =
      reg_nested_bank{update_nth_nested_bank<unsigned int>(0u, v, r.status_)};
  RamOps::chip_nested_bank c_ = chip_nested_bank{
      update_nth_nested_bank<RamOps::reg_nested_bank>(0u, r_, c.regs_)};
  RamOps::bank_nested_bank b_ = bank_nested_bank{
      update_nth_nested_bank<RamOps::chip_nested_bank>(0u, c_, b.chips_)};
  return state_nested_bank{
      update_nth_nested_bank<RamOps::bank_nested_bank>(0u, b_, s.banks_)};
}

__attribute__((pure)) unsigned int
RamOps::read_status0(const RamOps::state_nested_bank &s) {
  RamOps::bank_nested_bank b = get_bank0(s);
  RamOps::chip_nested_bank c = get_chip0(b);
  RamOps::reg_nested_bank r = get_reg0(c);
  return ListDef::template nth<unsigned int>(0u, r.status_, 0u);
}

__attribute__((pure)) unsigned int RamOps::score(const RamOps::Item x) {
  switch (x) {
  case Item::e_S_: {
    return 1u;
  }
  case Item::e_S_0: {
    return 2u;
  }
  default:
    std::unreachable();
  }
}
