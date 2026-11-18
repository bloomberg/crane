// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <tyarg_implicit_type_binder.h>
#include <cassert>

int main() {
  assert(TyargImplicitTypeBinder::selected == 4);
  assert(TyargImplicitTypeBinder::nil_len == 0);
  assert(TyargImplicitTypeBinder::both_fst == 2);
  return 0;
}
