#include <src_wrr_updates_rom_port.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int SrcWrrUpdatesRomPort::get_reg(
    const std::shared_ptr<SrcWrrUpdatesRomPort::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int SrcWrrUpdatesRomPort::get_reg_pair(
    const std::shared_ptr<SrcWrrUpdatesRomPort::state> &s,
    const unsigned int r) {
  unsigned int base =
      (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<SrcWrrUpdatesRomPort::state> SrcWrrUpdatesRomPort::execute_src(
    std::shared_ptr<SrcWrrUpdatesRomPort::state> s, const unsigned int r) {
  return std::make_shared<SrcWrrUpdatesRomPort::state>(state{
      s->regs, s->acc, s->rom_ports, (16u ? get_reg_pair(s, r) / 16u : 0)});
}

std::shared_ptr<SrcWrrUpdatesRomPort::state> SrcWrrUpdatesRomPort::execute_wrr(
    std::shared_ptr<SrcWrrUpdatesRomPort::state> s) {
  return std::make_shared<SrcWrrUpdatesRomPort::state>(state{
      s->regs, s->acc,
      update_nth<unsigned int>(s->sel_rom, s->acc, s->rom_ports), s->sel_rom});
}
