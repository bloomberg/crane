#include <src_wrr_rom_port_roundtrip.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int SrcWrrRomPortRoundtrip::get_reg(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

__attribute__((pure)) unsigned int SrcWrrRomPortRoundtrip::get_reg_pair(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<SrcWrrRomPortRoundtrip::state>
SrcWrrRomPortRoundtrip::execute_src(
    std::shared_ptr<SrcWrrRomPortRoundtrip::state> s, const unsigned int r) {
  return std::make_shared<SrcWrrRomPortRoundtrip::state>(
      state{s->regs, s->acc, s->rom_ports,
            Nat::div(get_reg_pair(s, std::move(r)), 16u)});
}

std::shared_ptr<SrcWrrRomPortRoundtrip::state>
SrcWrrRomPortRoundtrip::execute_wrr(
    std::shared_ptr<SrcWrrRomPortRoundtrip::state> s) {
  return std::make_shared<SrcWrrRomPortRoundtrip::state>(state{
      s->regs, s->acc,
      update_nth<unsigned int>(s->sel_rom, s->acc, s->rom_ports), s->sel_rom});
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
