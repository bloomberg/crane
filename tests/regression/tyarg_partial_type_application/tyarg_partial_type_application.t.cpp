// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <tyarg_partial_type_application.h>
#include <cassert>

int main() {
  assert(TyargPartialTypeApplication::bound.has_value());
  assert(*TyargPartialTypeApplication::bound == true);
  assert(TyargPartialTypeApplication::lifted.has_value());
  assert(*TyargPartialTypeApplication::lifted == 5);
  assert(TyargPartialTypeApplication::first_of_doubled == 1);
  return 0;
}
