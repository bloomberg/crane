// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <tyarg_family_binder_shift.h>
#include <cassert>

int main() {
  assert(TyargFamilyBinderShift::picked == 3);
  assert(TyargFamilyBinderShift::empty_len == 0);
  assert(TyargFamilyBinderShift::applied == 5);
  assert(TyargFamilyBinderShift::counted == 5);
  return 0;
}
