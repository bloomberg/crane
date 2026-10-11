// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <macro_named_constructor.h>
#include <cassert>

int main() {
  assert(MacroNamedConstructor::total == 8);
  assert(MacroNamedConstructor::two_is_normal);
  return 0;
}
