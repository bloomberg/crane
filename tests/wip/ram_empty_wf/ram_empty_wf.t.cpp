// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <ram_empty_wf.h>
int main() {
  assert(RamEmptyWf::default_bank_idx == 0u);
  assert(RamEmptyWf::default_sel->sel_bank == 0u);
  assert(RamEmptyWf::default_sel->sel_chip == 0u);
  assert(RamEmptyWf::default_sel->sel_reg == 0u);
  assert(RamEmptyWf::default_sel->sel_char == 0u);
  assert(RamEmptyWf::empty_chip->chip_port == 0u);
  return 0;
}
