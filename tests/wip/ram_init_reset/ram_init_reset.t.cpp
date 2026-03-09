// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <ram_init_reset.h>
int main() {
  assert(RamInitReset::reset_pc == 0u);
  assert(RamInitReset::init_state->state_acc == 0u);
  assert(RamInitReset::init_state->state_pc == 0u);
  assert(RamInitReset::init_state->state_carry == false);
  return 0;
}
