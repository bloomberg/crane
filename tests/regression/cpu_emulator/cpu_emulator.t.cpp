// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <cpu_emulator.h>
int main() {
  // sample: acc=3, regs[4]=5, carry=false
  assert(CpuEmulator::sample.ex_acc == 3u);
  // ADD 4: 3+5+0=8
  assert(CpuEmulator::add_result == 8u);
  // NOP preserves accumulator
  assert(CpuEmulator::nop_acc == 3u);
  // LDM 5: load immediate 5
  assert(CpuEmulator::ldm_result == 5u);
  // JUN 1024: jump to address 1024
  assert(CpuEmulator::jun_pc == 1024u);
  return 0;
}
