#include "src_wrr_updates_rom_port.h"

uint64_t SrcWrrUpdatesRomPort::get_reg(const SrcWrrUpdatesRomPort::state &s,
                                       uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.regs, UINT64_C(0));
}

uint64_t
SrcWrrUpdatesRomPort::get_reg_pair(const SrcWrrUpdatesRomPort::state &s,
                                   uint64_t r) {
  uint64_t base = (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
                        ? 0
                        : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
  return ((get_reg(s, base) * UINT64_C(16)) + get_reg(s, (base + UINT64_C(1))));
}

SrcWrrUpdatesRomPort::state
SrcWrrUpdatesRomPort::execute_src(const SrcWrrUpdatesRomPort::state &s,
                                  uint64_t r) {
  return state{s.regs, s.acc, s.rom_ports,
               (UINT64_C(16) ? get_reg_pair(s, r) / UINT64_C(16) : 0)};
}

SrcWrrUpdatesRomPort::state
SrcWrrUpdatesRomPort::execute_wrr(const SrcWrrUpdatesRomPort::state &s) {
  return state{s.regs, s.acc,
               update_nth<uint64_t>(s.sel_rom, s.acc, s.rom_ports), s.sel_rom};
}
