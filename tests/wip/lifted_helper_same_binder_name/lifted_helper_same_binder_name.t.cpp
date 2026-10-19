// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <lifted_helper_same_binder_name.h>
#include <cassert>

int main() {
  assert(LiftedHelperSameBinderName::t1 == 4);
  assert(LiftedHelperSameBinderName::t2 == 2);
  assert(LiftedHelperSameBinderName::two(false, 7) == 2);
  return 0;
}
