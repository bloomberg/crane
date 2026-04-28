#include <ram_state_ops.h>

__attribute__((pure)) RamStateOps::state
RamStateOps::reset_state(const RamStateOps::state &s) {
  return state{
      s.state_regs, 0u,          false,      0u, List<unsigned int>::nil(),
      s.state_ram,  default_sel, s.state_rom};
}

__attribute__((pure)) unsigned int
RamStateOps::get_main(const RamStateOps::ram_reg &rg, const unsigned int &i) {
  return ListDef::template nth<unsigned int>(i, rg.reg_main, 0u);
}

__attribute__((pure)) unsigned int
RamStateOps::get_stat(const RamStateOps::ram_reg &rg, const unsigned int &i) {
  return ListDef::template nth<unsigned int>(i, rg.reg_status, 0u);
}

__attribute__((pure)) RamStateOps::ram_reg
RamStateOps::upd_main_in_reg(const RamStateOps::ram_reg &rg,
                             const unsigned int &i, const unsigned int &v) {
  return ram_reg{update_nth<unsigned int>(i, (16u ? v % 16u : v), rg.reg_main),
                 rg.reg_status};
}

__attribute__((pure)) RamStateOps::ram_reg
RamStateOps::upd_stat_in_reg(const RamStateOps::ram_reg &rg,
                             const unsigned int &i, const unsigned int &v) {
  return ram_reg{rg.reg_main, update_nth<unsigned int>(i, (16u ? v % 16u : v),
                                                       rg.reg_status)};
}

__attribute__((pure)) RamStateOps::ram_reg
RamStateOps::get_regRAM(const RamStateOps::ram_chip &ch,
                        const unsigned int &r) {
  return ListDef::template nth<RamStateOps::ram_reg>(r, ch.chip_regs,
                                                     empty_reg);
}

__attribute__((pure)) RamStateOps::ram_chip
RamStateOps::upd_reg_in_chip(const RamStateOps::ram_chip &ch,
                             const unsigned int &r,
                             const RamStateOps::ram_reg &rg) {
  return ram_chip{update_nth<RamStateOps::ram_reg>(r, rg, ch.chip_regs),
                  ch.chip_port};
}

__attribute__((pure)) RamStateOps::ram_chip
RamStateOps::upd_port_in_chip(const RamStateOps::ram_chip &ch,
                              const unsigned int &v) {
  return ram_chip{ch.chip_regs, (16u ? v % 16u : v)};
}

__attribute__((pure)) RamStateOps::ram_chip
RamStateOps::get_chip(const RamStateOps::ram_bank &bk, const unsigned int &c) {
  return ListDef::template nth<RamStateOps::ram_chip>(c, bk.bank_chips,
                                                      empty_chip);
}

__attribute__((pure)) RamStateOps::ram_bank
RamStateOps::upd_chip_in_bank(const RamStateOps::ram_bank &bk,
                              const unsigned int &c,
                              const RamStateOps::ram_chip &ch) {
  return ram_bank{update_nth<RamStateOps::ram_chip>(c, ch, bk.bank_chips)};
}

__attribute__((pure)) RamStateOps::ram_bank
RamStateOps::get_bank_from_sys(const List<RamStateOps::ram_bank> &sys,
                               const unsigned int &b) {
  return ListDef::template nth<RamStateOps::ram_bank>(b, sys, empty_bank);
}

__attribute__((pure)) List<RamStateOps::ram_bank>
RamStateOps::upd_bank_in_sys(const RamStateOps::state &s, const unsigned int &b,
                             const RamStateOps::ram_bank &bk) {
  return update_nth<RamStateOps::ram_bank>(b, bk, s.state_ram);
}

__attribute__((pure)) RamStateOps::ram_bank
RamStateOps::current_bank(const RamStateOps::state &s) {
  return get_bank_from_sys(s.state_ram, s.state_sel.sel_bank);
}

__attribute__((pure)) RamStateOps::ram_chip
RamStateOps::current_chip(const RamStateOps::state &s) {
  return get_chip(current_bank(s), s.state_sel.sel_chip);
}

__attribute__((pure)) RamStateOps::ram_reg
RamStateOps::current_reg(const RamStateOps::state &s) {
  return get_regRAM(current_chip(s), s.state_sel.sel_reg);
}

__attribute__((pure)) unsigned int
RamStateOps::ram_read_main(const RamStateOps::state &s) {
  return get_main(current_reg(s), s.state_sel.sel_char);
}

__attribute__((pure)) List<RamStateOps::ram_bank>
RamStateOps::ram_write_main_sys(const RamStateOps::state &s,
                                const unsigned int &v) {
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

__attribute__((pure)) List<RamStateOps::ram_bank>
RamStateOps::ram_write_status_sys(const RamStateOps::state &s,
                                  const unsigned int &idx,
                                  const unsigned int &v) {
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

__attribute__((pure)) std::pair<std::optional<unsigned int>, RamStateOps::state>
RamStateOps::pop_stack(RamStateOps::state s) {
  auto &&_sv = s.state_stack;
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return std::make_pair(std::optional<unsigned int>(), std::move(s));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    return std::make_pair(std::make_optional<unsigned int>(d_a0),
                          state{s.state_regs, s.state_acc, s.state_carry,
                                s.state_pc, *(d_a1), s.state_ram, s.state_sel,
                                s.state_rom});
  }
}
