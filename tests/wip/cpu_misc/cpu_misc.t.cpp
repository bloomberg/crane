// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <cpu_misc.h>
int main() {
  assert(CpuMisc::ldm_result == 5u);
  return 0;
}
