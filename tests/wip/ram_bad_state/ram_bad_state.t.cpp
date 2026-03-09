// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <ram_bad_state.h>
int main() {
  assert(RamBadState::overflow_acc == 16u);
  assert(RamBadState::bad_state_acc_overflow->state_acc == 16u);
  assert(RamBadState::bad_state_pc_overflow->state_pc == 4096u);
  assert(RamBadState::bad_state_wrong_reg_count->state_acc == 0u);
  return 0;
}
