// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <module_alias_target_handling.h>
#include <cassert>

int main() {
  assert(ModuleAliasTargetHandling::mapped == 4);
  assert(ModuleAliasTargetHandling::methodified == 3);
  return 0;
}
