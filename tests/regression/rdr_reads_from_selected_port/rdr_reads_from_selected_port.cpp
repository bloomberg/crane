#include <rdr_reads_from_selected_port.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<RdrReadsFromSelectedPort::state>
RdrReadsFromSelectedPort::execute_rdr(
    const std::shared_ptr<RdrReadsFromSelectedPort::state> &s) {
  return std::make_shared<RdrReadsFromSelectedPort::state>(
      state{ListDef::template nth<unsigned int>(s->sel_rom, s->rom_ports, 0u),
            s->rom_ports, s->sel_rom});
}
