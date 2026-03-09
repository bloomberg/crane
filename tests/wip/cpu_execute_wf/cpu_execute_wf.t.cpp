// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <cpu_execute_wf.h>
int main() {
  // sample: acc=3, regs[4]=5, carry=false. ADD 4: 3+5+0=8.
  assert(CpuExecuteWf::add_result == 8u);
  assert(CpuExecuteWf::sample->ex_acc == 3u);
  return 0;
}
