// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <module_type_short_name_clash.h>
#include <cassert>

int main() {
  assert(ModuleTypeShortNameClash::result == 6);
  return 0;
}
