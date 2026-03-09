// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <cpu_instr_wf.h>
int main() {
  // NOP preserves accumulator: sample has acc=3
  assert(CpuInstrWf::nop_acc == 3u);
  return 0;
}
