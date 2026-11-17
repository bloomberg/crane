// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <method_lifted_helper_same_name.h>
#include <cassert>

int main() {
  // sample = {| nats := [1; 2]; flags := [true] |}: total counts each element
  // once, doubled twice.
  assert(MethodLiftedHelperSameName::t1 == 3);
  assert(MethodLiftedHelperSameName::t2 == 6);
  return 0;
}
