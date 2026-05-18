#include "reset_state.h"

ResetState::state_full
ResetState::reset_state_full(const ResetState::state_full &s) {
  return state_full{UINT64_C(0),           s.regs_full, false, UINT64_C(0),
                    List<uint64_t>::nil(), s.ram_sys,   s.rom};
}

ResetState::state_minimal
ResetState::reset_state_minimal(const ResetState::state_minimal &s) {
  return state_minimal{s.regs_minimal, false, UINT64_C(0), s.ram_sys_minimal,
                       s.rom_minimal};
}
