// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <itree_ret_family_from_result.h>
#include <cassert>

int main() {
  assert(ItreeRetFamilyFromResult::ok_result == 3);
  assert(ItreeRetFamilyFromResult::raises_result == 107);
  return 0;
}
