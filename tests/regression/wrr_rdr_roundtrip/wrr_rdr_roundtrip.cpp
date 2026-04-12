#include <wrr_rdr_roundtrip.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<WrrRdrRoundtrip::state>
WrrRdrRoundtrip::execute_wrr(const std::shared_ptr<WrrRdrRoundtrip::state> &s) {
  return std::make_shared<WrrRdrRoundtrip::state>(
      state{s->acc, update_nth<unsigned int>(s->sel_rom, s->acc, s->rom_ports),
            s->sel_rom});
}

std::shared_ptr<WrrRdrRoundtrip::state>
WrrRdrRoundtrip::execute_rdr(const std::shared_ptr<WrrRdrRoundtrip::state> &s) {
  return std::make_shared<WrrRdrRoundtrip::state>(
      state{s->rom_ports->nth(s->sel_rom, 0u), s->rom_ports, s->sel_rom});
}
