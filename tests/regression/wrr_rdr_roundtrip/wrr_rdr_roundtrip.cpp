#include "wrr_rdr_roundtrip.h"

WrrRdrRoundtrip::state
WrrRdrRoundtrip::execute_wrr(const WrrRdrRoundtrip::state &s) {
  return state{s.acc, update_nth<uint64_t>(s.sel_rom, s.acc, s.rom_ports),
               s.sel_rom};
}

WrrRdrRoundtrip::state
WrrRdrRoundtrip::execute_rdr(const WrrRdrRoundtrip::state &s) {
  return state{
      ListDef::template nth<uint64_t>(s.sel_rom, s.rom_ports, UINT64_C(0)),
      s.rom_ports, s.sel_rom};
}
