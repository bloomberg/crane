// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <same_named_file_modules.h>
#include <cassert>

int main() {
  assert(SameNamedFileModules::found == 2);
  assert(SameNamedFileModules::larger);
  return 0;
}
