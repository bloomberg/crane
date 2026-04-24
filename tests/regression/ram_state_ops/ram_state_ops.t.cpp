// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <ram_state_ops.h>

#include <cassert>

int main() {
  auto v = RamStateOps::get_stat(RamStateOps::empty_reg, 2u);
  assert(v == 0u);

  auto rs = RamStateOps::reset_state(RamStateOps::cleared_state);
  assert(rs.state_acc == 0u);
  assert(rs.state_carry == false);
  assert(rs.state_pc == 0u);

  assert(RamStateOps::t == 0u);

  return 0;
}
