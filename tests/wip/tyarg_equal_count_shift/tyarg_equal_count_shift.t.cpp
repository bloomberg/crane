// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <tyarg_equal_count_shift.h>
#include <cassert>

int main() {
  assert(TyargEqualCountShift::chosen == true);
  assert(TyargEqualCountShift::chosen_nat == 9);
  assert(TyargEqualCountShift::full_pick == false);
  return 0;
}
