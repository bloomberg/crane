#include <rdr_reads_from_selected_port.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) RdrReadsFromSelectedPort::state
RdrReadsFromSelectedPort::execute_rdr(
    const RdrReadsFromSelectedPort::state &s) {
  return state{ListDef::template nth<unsigned int>(s.sel_rom, s.rom_ports, 0u),
               s.rom_ports, s.sel_rom};
}
