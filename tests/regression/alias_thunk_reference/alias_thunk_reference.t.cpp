// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <alias_thunk_reference.h>
#include <cassert>

int main() {
  assert(AliasThunkReference::from_cofix == 1);
  assert(AliasThunkReference::from_throwing == 9);
  return 0;
}
