// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <three_argument_curried_slot.h>
#include <cassert>

int main() {
  assert(ThreeArgumentCurriedSlot::result == 6 + 3);
  return 0;
}
