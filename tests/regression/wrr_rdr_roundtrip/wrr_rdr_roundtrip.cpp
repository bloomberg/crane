#include <wrr_rdr_roundtrip.h>

WrrRdrRoundtrip::state
WrrRdrRoundtrip::execute_wrr(const WrrRdrRoundtrip::state &s) {
  return state{s.acc, update_nth<unsigned int>(s.sel_rom, s.acc, s.rom_ports),
               s.sel_rom};
}

WrrRdrRoundtrip::state
WrrRdrRoundtrip::execute_rdr(const WrrRdrRoundtrip::state &s) {
  return state{ListDef::template nth<unsigned int>(s.sel_rom, s.rom_ports, 0u),
               s.rom_ports, s.sel_rom};
}
