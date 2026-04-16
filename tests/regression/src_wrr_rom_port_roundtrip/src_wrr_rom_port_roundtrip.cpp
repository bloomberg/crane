#include <src_wrr_rom_port_roundtrip.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int SrcWrrRomPortRoundtrip::get_reg(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s,
    const unsigned int r) {
  return ListDef::template nth<unsigned int>(r, s->regs, 0u);
}

__attribute__((pure)) unsigned int SrcWrrRomPortRoundtrip::get_reg_pair(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s,
    const unsigned int r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<SrcWrrRomPortRoundtrip::state>
SrcWrrRomPortRoundtrip::execute_src(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s,
    const unsigned int r) {
  return std::make_shared<SrcWrrRomPortRoundtrip::state>(state{
      s->regs, s->acc, s->rom_ports, (16u ? get_reg_pair(s, r) / 16u : 0)});
}

std::shared_ptr<SrcWrrRomPortRoundtrip::state>
SrcWrrRomPortRoundtrip::execute_wrr(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s) {
  return std::make_shared<SrcWrrRomPortRoundtrip::state>(state{
      s->regs, s->acc,
      update_nth<unsigned int>(s->sel_rom, s->acc, s->rom_ports), s->sel_rom});
}
