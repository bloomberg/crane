#include <src_wrr_updates_rom_port.h>

unsigned int SrcWrrUpdatesRomPort::get_reg(const SrcWrrUpdatesRomPort::state &s,
                                           const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

unsigned int
SrcWrrUpdatesRomPort::get_reg_pair(const SrcWrrUpdatesRomPort::state &s,
                                   const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

SrcWrrUpdatesRomPort::state
SrcWrrUpdatesRomPort::execute_src(const SrcWrrUpdatesRomPort::state &s,
                                  const unsigned int &r) {
  return state{s.regs, s.acc, s.rom_ports,
               (16u ? get_reg_pair(s, r) / 16u : 0)};
}

SrcWrrUpdatesRomPort::state
SrcWrrUpdatesRomPort::execute_wrr(const SrcWrrUpdatesRomPort::state &s) {
  return state{s.regs, s.acc,
               update_nth<unsigned int>(s.sel_rom, s.acc, s.rom_ports),
               s.sel_rom};
}
