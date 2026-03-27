// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <program_wf_prop.h>

#include <cassert>

int main() {
  auto jt =
      ProgramWfProp::jump_target(ProgramWfProp::instruction::jun(100u));
  assert(jt.has_value() && *jt == 100u);
  assert(!ProgramWfProp::jump_target(ProgramWfProp::instruction::nop())
              .has_value());
  return 0;
}
