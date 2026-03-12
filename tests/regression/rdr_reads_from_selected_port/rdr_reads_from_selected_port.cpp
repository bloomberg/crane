#include <rdr_reads_from_selected_port.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<RdrReadsFromSelectedPort::state>
RdrReadsFromSelectedPort::execute_rdr(
    std::shared_ptr<RdrReadsFromSelectedPort::state> s) {
  return std::make_shared<RdrReadsFromSelectedPort::state>(
      state{s->rom_ports->nth(s->sel_rom, 0u), s->rom_ports, s->sel_rom});
}
