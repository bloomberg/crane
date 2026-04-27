#include <src_wrr_rom_port_roundtrip.h>

__attribute__((pure)) unsigned int
SrcWrrRomPortRoundtrip::get_reg(const SrcWrrRomPortRoundtrip::state &s,
                                const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.regs, 0u);
}

__attribute__((pure)) unsigned int
SrcWrrRomPortRoundtrip::get_reg_pair(const SrcWrrRomPortRoundtrip::state &s,
                                     const unsigned int &r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

__attribute__((pure)) SrcWrrRomPortRoundtrip::state
SrcWrrRomPortRoundtrip::execute_src(const SrcWrrRomPortRoundtrip::state &s,
                                    const unsigned int &r) {
  return state{s.regs, s.acc, s.rom_ports,
               (16u ? get_reg_pair(s, r) / 16u : 0)};
}

__attribute__((pure)) SrcWrrRomPortRoundtrip::state
SrcWrrRomPortRoundtrip::execute_wrr(const SrcWrrRomPortRoundtrip::state &s) {
  return state{s.regs, s.acc,
               update_nth<unsigned int>(s.sel_rom, s.acc, s.rom_ports),
               s.sel_rom};
}
