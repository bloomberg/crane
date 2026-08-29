#include "rdr_reads_from_selected_port.h"

RdrReadsFromSelectedPort::state RdrReadsFromSelectedPort::execute_rdr(
    const RdrReadsFromSelectedPort::state &s) {
  return state{
      ListDef::template nth<uint64_t>(s.sel_rom, s.rom_ports, UINT64_C(0)),
      s.rom_ports, s.sel_rom};
}
