// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <program_wf.h>
int main() {
  assert(ProgramWf::sample_code_size == 20u);
  assert(ProgramWf::sample_layout->base_addr == 200u);
  assert(ProgramWf::sample_layout->code_size == 20u);
  return 0;
}
