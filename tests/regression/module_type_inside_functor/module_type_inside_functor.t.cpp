// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <module_type_inside_functor.h>
#include <cassert>

int main() {
  assert(ModuleTypeInsideFunctor::result == 7);
  return 0;
}
