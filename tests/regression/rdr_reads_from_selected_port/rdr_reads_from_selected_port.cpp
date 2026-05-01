#include <rdr_reads_from_selected_port.h>

RdrReadsFromSelectedPort::state RdrReadsFromSelectedPort::execute_rdr(
    const RdrReadsFromSelectedPort::state &s) {
  return state{ListDef::template nth<unsigned int>(s.sel_rom, s.rom_ports, 0u),
               s.rom_ports, s.sel_rom};
}
