#include "ram_init_reset.h"

RamInitReset::state RamInitReset::reset_state(const RamInitReset::state &s) {
  return state{s.state_regs,          UINT64_C(0), false,       UINT64_C(0),
               List<uint64_t>::nil(), s.state_ram, default_sel, s.state_rom};
}

std::pair<std::optional<uint64_t>, RamInitReset::state>
RamInitReset::pop_stack(RamInitReset::state s) {
  auto &&_sv = s.state_stack;
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::make_pair(std::optional<uint64_t>(), std::move(s));
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    return std::make_pair(std::make_optional<uint64_t>(a0),
                          state{s.state_regs, s.state_acc, s.state_carry,
                                s.state_pc, *a1, s.state_ram, s.state_sel,
                                s.state_rom});
  }
}
