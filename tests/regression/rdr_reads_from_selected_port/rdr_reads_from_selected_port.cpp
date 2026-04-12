#include <rdr_reads_from_selected_port.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<RdrReadsFromSelectedPort::state>
RdrReadsFromSelectedPort::execute_rdr(
    const std::shared_ptr<RdrReadsFromSelectedPort::state> &s) {
  return std::make_shared<RdrReadsFromSelectedPort::state>(
      state{s->rom_ports->nth(s->sel_rom, 0u), s->rom_ports, s->sel_rom});
}
