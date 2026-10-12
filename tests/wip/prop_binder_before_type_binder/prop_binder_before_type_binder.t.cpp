// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <prop_binder_before_type_binder.h>
#include <cassert>

int main() {
  assert(PropBinderBeforeTypeBinder::picked == 5);
  assert(PropBinderBeforeTypeBinder::second == 5);
  assert(PropBinderBeforeTypeBinder::guard_sum == 12);
  assert(PropBinderBeforeTypeBinder::selected == 6);
  return 0;
}
