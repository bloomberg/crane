#include <reset_state.h>

ResetState::state_full
ResetState::reset_state_full(const ResetState::state_full &s) {
  return state_full{
      0u, s.regs_full, false, 0u, List<unsigned int>::nil(), s.ram_sys, s.rom};
}

ResetState::state_minimal
ResetState::reset_state_minimal(const ResetState::state_minimal &s) {
  return state_minimal{s.regs_minimal, false, 0u, s.ram_sys_minimal,
                       s.rom_minimal};
}
