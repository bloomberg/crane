// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <fix_let_binder_self_reference.h>
#include <cassert>

int main() {
  assert(FixLetBinderSelfReference::result == 5);
  return 0;
}
